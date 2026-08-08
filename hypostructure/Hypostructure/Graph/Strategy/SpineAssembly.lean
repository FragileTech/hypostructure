import Hypostructure.Graph.Strategy.TypeAExitRun

/-!
# The entry spine, composed

The rows of `SpineRows` are each quantified over the keys they consume and
produce.  This module installs them all at the spine's own vocabulary and runs
them in the manuscript's order against the one canonical ledger, from opening
the minimal-counterexample scope at node `[1]` through the rank-drop decision
at node `[32]` and into Branch D, up to the context-validity test `[36]` and
its closed terminal `[37]`.

The full-rank residual of node `[34]` is no longer an exit: the block carries it
on through the forced curvature cost `[47]`--`[48]`, the per-vertex remainder
entropy split `[49]`--`[50]`, the two-budget accounting `[51]`--`[52]`, the
admissible entropy cap `[53]` and its terminal `[54]`, Residual C `[55]`--`[56]`,
and the net-charge continuation `[57]`--`[64]`.

The result type is the statement being made.  Each constructor of `Result` is
one exit of the block:

* the surplus split at node `[19]` sends a non-near-cubic object out of the
  block, with everything proved up to that point;
* the barrier comparison at node `[21]` sends an overflowing object out of the
  block, with everything proved up to that point;
* the rank comparison at node `[32]` enters Branch D, which the block carries
  through nodes `[33]`--`[46]`: the determination certificate, the
  context-validity test `[36]`, the atom-compression test `[38]`, the
  delocalization-scope test `[41]`, the repair identity `[44]` and the global
  barrier `[45]`.  Part III's caption is *"every rank-drop branch terminates in
  a closed round node"*, and all four of its terminals -- `[37]`, `[39]`, `[42]`
  and `[46]` -- close here, so Branch D leaves no open leaf;
* the two arms of the entropy split `[50]` each reach the entropy-cap terminal
  `[54]`, one through node `[52]`'s package accounting and one through node
  `[53]`'s own comparison;
* the nonnegative arm of the net-charge test `[59]` leaves on node `[60]`'s
  window-join pressure;
* and its negative arm reaches the Type A and Type B residuals `[63]` and
  `[64]`, on which the local analysis continues.

A branch that left at `[19]` has no `[21]` fact in its index and vice versa,
neither exit of `[32]` carries the other's arm, neither exit of `[36]` carries
the other's, and neither exit of `[50]`, `[53]`, `[59]` or `[62]` carries its
own sibling's.  Nothing is carried between rows but the residual and the
ledger.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The closure key is not a semantic fact.  Every freshness condition on a
closure entry is discharged through this. -/
@[simp] theorem closed_ne_key (k : Key) :
    (closed : FactKey (Input BranchState Presentation presentation data)) ≠
      K k := by
  intro same
  cases same

/-- Distinct semantic keys are distinct exact keys.  Every freshness and
distinctness side condition below is discharged through this, so a disequality
is decided on the vocabulary's own finite `Key` and never on the residual
domain, which contains free parameters and cannot be evaluated. -/
@[simp] theorem key_inj {left right : Key} :
    (K left : FactKey (Input BranchState Presentation presentation data)) =
        K right ↔ left = right := by
  constructor
  · intro same; injection same
  · intro same; rw [same]

section Rows

variable (T : Core.Target (problem BranchState Presentation presentation data))
variable (targetPredicate :
  T.Predicate = Graph.HasCycleWithLength data.LengthOK)

/-- **The target's isomorphism invariance is derived, not assumed.**

Node `[11]`--`[14]` needs the target predicate to be invariant under the
problem's own semantic equivalence.  That is not a hypothesis of the spine: the
graph layer proves it once, in `Graph.hasCycleWithLength_iff_of_iso`, and
`Graph.minimumDegreeCycleTargetInvariant` packages it as the `Core.TargetInvariant`
this row consumes.  With `targetPredicate` identifying `T.Predicate` with the
cycle target, the invariance transports to `T` by rewriting.

An earlier revision took this as a parameter of `run`.  That let a caller supply
a mathematical fact the framework already owns -- exactly the "supplied field
standing in for a derivation" the Facts column forbids -- so it is derived
here. -/
noncomputable def spineTargetInvariant
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK) :
    Core.TargetInvariant
      (Graph.isomorphismEquivalenceWithPresentation
        (Graph.MinimumDegreeAtLeast data.threshold) BranchState
        Presentation presentation
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
      T.Predicate :=
  targetPredicate ▸
    Graph.minimumDegreeCycleTargetInvariant data.threshold BranchState
      Presentation presentation data.LengthOK

/-- Nodes `[5]`--`[7]`, at the spine's own keys. -/
@[reducible] noncomputable def returnAvoidance :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  returnAvoidanceRow (K .selection) (K .returnAvoidance) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[8]`. -/
@[reducible] noncomputable def noProperBaseline :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  noProperBaselineRow (K .selection) (K .noProperBaseline) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.2)
    (fun _input value => ⟨value⟩)

/-- Nodes `[89]`--`[94]`: `lem:typeA-port-return`, the port non-vacuity. -/
@[reducible] noncomputable def typeAPortReturn :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeAPortReturnRow (K .selection) (K .typeAPortReturn) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.2)
    (fun _input value => ⟨value⟩)

/-- Node `[91]`: the exact `3/7/11` discharging inequality. -/
@[reducible] noncomputable def typeAUnsaturatedDischarge :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeAUnsaturatedDischargeRow (K .typeAReceiverRouting)
    (K .typeAUnsaturatedReceivers) (K .typeAUnsaturatedDischarge) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[91]` closes because its nonnegative discharging conclusion is
incompatible with the retained negative Type A support. -/
noncomputable instance typeAUnsaturatedDischargeClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .typeALowSurplus)
      (K (data := data) .typeAUnsaturatedDischarge) where
  contradiction := fun _input _low discharged => by
    obtain ⟨_packing, _valid, _maximal, _component, _present, negative,
      surplus, nonnegative⟩ := discharged.down
    unfold Graph.FiniteObject.NegativeNetCharge at negative
    rw [surplus, Nat.mul_zero, Nat.add_zero] at negative
    omega

/-- Node `[104]`: exit `(5)` closes against `cor:uncompressible`. -/
noncomputable instance typeAExitFiveClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .uncompressible)
      (K (data := data) .typeAExitFive) where
  contradiction := fun _input uncompressible exitFive => by
    obtain ⟨_packing, _valid, _maximal, _component, _present, _negative,
      _zero, _receiver, _isReceiver, _peeled, _peeledSubset, _saturated,
      _noExitFour, support, compressible⟩ := exitFive.down
    exact (uncompressible.down support) compressible

/-- Node `[93]`, yes arm: clause (Q1) of `def:typeA-exit4-family`. -/
@[reducible] noncomputable def typeAVisibleEntryClause :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeAVisibleEntryClauseRow (K .typeAVisibleEntry)
    (K .typeAVisibleEntryClause) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Nodes `[9]`--`[10]`. -/
@[reducible] noncomputable def deletionCriticality :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  deletionCriticalityRow (K .noProperBaseline) (K .tightEndpoint)
    (K .slackIndependent) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Nodes `[11]`--`[14]`. -/
@[reducible] noncomputable def interfaceReplacement :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  interfaceReplacementRow T (spineTargetInvariant T targetPredicate)
    (K .selection) (K .uncompressible)
    (by simp)
    (fun _input fact => by rw [targetPredicate]; exact fact.down.1)
    (fun _input fact smaller smallerLt baseline => by
      rw [targetPredicate]; exact fact.down.2 smaller smallerLt baseline)
    (fun _input value =>
      ⟨show ∀ support : Finset _input.object.Vertex,
          ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) _input.object support
        from targetPredicate ▸ value⟩)

/-- Nodes `[15]`--`[17]`. -/
@[reducible] noncomputable def obstructionPacking :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  obstructionPackingRow (K .selection) (K .maximalPacking) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[18]`. -/
@[reducible] noncomputable def localAlgebra :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  localAlgebraRow (K .localAlgebra)
    (fun _input value => ⟨value⟩)

/-- Nodes `[25]`--`[27]`. -/
@[reducible] noncomputable def remainderNormalization :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  remainderNormalizationRow (K .selection) (K .remainderNormalized) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Nodes `[22]`--`[24]`. -/
@[reducible] noncomputable def densityBudget :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  densityBudgetRow (K .barrierCap) (K .surplusAtOrBelow) (K .densityCap)
    (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Nodes `[28]`--`[29]`. -/
@[reducible] noncomputable def boundaryDemand :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  boundaryDemandRow (K .remainderNormalized) (K .surplusAtOrBelow)
    (K .boundaryDemand) (K .stubSupply)
    (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Node `[30]`. -/
@[reducible] noncomputable def wedgeSupply :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  wedgeSupplyRow (K .boundaryDemand) (K .wedgeSupply) (K .curvatureDemandFloor)
    (by simp) (by simp) (by simp)
    -- The row-38 chain, composed into the single ceiling this row substitutes.
    (fun _input fact packing valid => by
      have chain := fact.down packing valid
      omega)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Node `[31]`. -/
@[reducible] noncomputable def curvatureTargetRank :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  curvatureTargetRankRow (K .curvatureDemandFloor) (K .curvatureTargetRank)
    (by simp) (fun _input value => ⟨value⟩)

/-- Nodes `[33]` and `[35]`: Branch D, entered with its certificate. -/
@[reducible] noncomputable def branchDependence :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  branchDependenceRow (K .curvatureRankDrop) (K .branchDependence) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Nodes `[47]`--`[48]`. -/
@[reducible] noncomputable def forcedCurvatureCost :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  forcedCurvatureCostRow (K .curvatureDemandFloor) (K .curvatureFullRank)
    (K .forcedCurvatureCost) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[52]`. -/
@[reducible] noncomputable def entropyPackage :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  entropyPackageRow (K .remainderEntropyHigh) (K .entropyPackageDemand)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Every low-entropy survivor has the same paper continuation.  The optional
local-type-vector analysis may add curvature information, but
`rem:closure-robust` records that the later large-budget route does not consume
that optional fact.  This row therefore commits only the common Residual C
conclusion and leaves the complete incoming ledger intact. -/
@[reducible] noncomputable def lowEntropyLargeBudget :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  lowEntropyLargeBudgetRow (K .remainderEntropyLow) (K .largeBudgetResidual)
    (by simp) (fun _input fact => fact.down)
    (fun _input low => ⟨Or.inr low⟩)

/-- Node `[60]`: the ordinary eventual net-charge cap. -/
@[reducible] noncomputable def netChargeCap :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  netChargeCapRow (data := data) (K .densityCap) (K .stubSupply)
    (K .netChargeLarge) (K .netChargeCap) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Nodes `[57]`--`[58]`. -/
@[reducible] noncomputable def netChargeLocalization :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  netChargeLocalizationRow (data := data) (K .netChargeLocalization)
    (fun _input value => ⟨value⟩)

/-- Node `[60]`. -/
@[reducible] noncomputable def windowJoinPressure :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  windowJoinPressureRow (K .netChargeNonNegative) (K .boundaryDemand)
    (K .windowJoinPressure) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[61]`. -/
@[reducible] noncomputable def negativeSupport :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  negativeSupportRow (K .netChargeNegative) (K .netChargeLocalization)
    (K .negativeSupport) (by simp) (fun _input fact => fact.down)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[88]`. -/
@[reducible] noncomputable def typeAReceiverRouting :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeAReceiverRoutingRow (K .remainderNormalized) (K .typeAReceiverRouting)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[68]`, the standing law both arms of the degree split read. -/
@[reducible] noncomputable def highCentreNormalForm :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  highCentreNormalFormRow (K .selection) (K .tightEndpoint)
    (K .highCentreNormalForm) (by simp)
    (fun _input fact => fact.down.1) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[69]`, on the heavy arm of node `[68]`. -/
@[reducible] noncomputable def heavyCentreLocalDichotomy :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  heavyCentreLocalDichotomyRow (K .highCentreNormalForm)
    (K .typeBHeavyCentre) (K .typeBLocalDichotomy) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[70]`, on both arms of node `[68]`.  One executor value, run after
either branch cursor: an `AtomicCT` has no predecessor parameter. -/
@[reducible] noncomputable def fanCertificateCap :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  fanCertificateCapRow (K .fanCertificateCap) (fun _input value => ⟨value⟩)

/-- Node `[74]`/`[82]`, on the B2 arm of node `[72]`/`[81]`.  One executor value,
run after either of the two B2 cursors. -/
@[reducible] noncomputable def hybridEntry :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  hybridEntryRow (K .selection) (K .fanCertificateCap) (K .fanCertificateMarked)
    (K .typeBHybridEntry) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down.1) (fun _input fact => fact.down)
    (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Nodes `[78]`--`[79]`, on the degree-four arm of node `[68]`. -/
@[reducible] noncomputable def degreeFourProfile :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  degreeFourProfileRow (K .highCentreNormalForm) (K .typeBDegreeFourCentres)
    (K .typeBDegreeFourProfile) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Node `[76]`/`[85]`, the exact disjoint post-ledger component fact. -/
@[reducible] noncomputable def disjointPostLedgerComponents :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  disjointPostLedgerComponentsRow (K .typeBB2Choice) (K .selection)
    (K .remainderNormalized) (K .typeBDisjointLedger) (by simp)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Nodes `[73]`/`[75]` and `[83]`/`[84]`, run on each Type B bridge residual
cursor that the local fan walk produces. -/
@[reducible] noncomputable def bridgeFanMass :
    (bridgeResidual :
      FactKey (Input BranchState Presentation presentation data)) →
    bridgeResidual ≠ K .typeBBridgeMass →
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  fun bridgeResidual distinct =>
  bridgeFanMassRow bridgeResidual (K .typeBBridgeMass) distinct
    (fun _input _bridgeResidual value => ⟨value⟩)

end Rows

/-- Nodes `[44]` and `[45]`: the repair identity and the global barrier. -/
@[reducible] noncomputable def globalBarrier :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  globalBarrierRow (K .globalDelocalization) (K .repairIdentity)
    (K .globalBarrier) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- **The terminals `[39]`, `[42]` and `[46]` close against the selection.**

Each names a determination certificate on the selected object, and
`not_branchDCertificate` refutes it: `cor:uncompressible` kills the
proper-support readings and the selection's own minimality kills the closed
representative.  Both halves of the selection fact are used -- its avoidance and
its minimality -- so the closure is genuinely a collision between the terminal
and the object the block selected, not a fact contradicting itself. -/
noncomputable instance instIncompatibleAtomCompression :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .atomCompression) where
  contradiction := fun residual selected compression =>
    not_branchDCertificate residual.object residual.baseline
      residual.branchState selected.down.1 selected.down.2
      (by
        obtain ⟨packing, valid, quotient, certified, _complete, _inside⟩ :=
          compression.down
        exact ⟨packing, valid, quotient, certified⟩)

noncomputable instance instIncompatibleProperDelocalization :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .properDelocalization) where
  contradiction := fun residual selected smearing =>
    not_branchDCertificate residual.object residual.baseline
      residual.branchState selected.down.1 selected.down.2
      (by
        obtain ⟨packing, valid, quotient, certified, _complete, _outside,
          _proper⟩ := smearing.down
        exact ⟨packing, valid, quotient, certified⟩)

noncomputable instance instIncompatibleGlobalBarrier :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .globalBarrier) where
  contradiction := fun residual selected barrier => by
    -- The reading node `[45]` committed is read back, not recomputed: this is
    -- the one place `lem:no-silent-global-smearing`'s disjunction is consumed,
    -- and the row that produced it is the one place it was derived.
    obtain ⟨_packing, _valid, _quotient, _certified, reading⟩ := barrier.down
    exact not_globalBarrierReading residual.baseline residual.branchState
      selected.down.1 selected.down.2 reading

noncomputable instance instIncompatibleTypeAExitSixProper :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .typeAExitSixProper) where
  contradiction := fun residual selected proper => by
    obtain ⟨_support, replacement⟩ := proper.down
    exact not_globalBarrierReading residual.baseline residual.branchState
      selected.down.1 selected.down.2 (Or.inl replacement)

noncomputable instance instIncompatibleTypeAExitSixGlobal :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .typeAExitSixGlobal) where
  contradiction := fun residual selected global => by
    exact not_globalBarrierReading residual.baseline residual.branchState
      selected.down.1 selected.down.2
      (support := (∅ : Finset residual.object.Vertex)) (Or.inr global.down)

/-- **The node-`[72]` closing arm is uninhabited**, at the spine's own keys.

`lem:typeB-direct-fan-window-cycles` and `lem:typeB-two-window-cycles` *build* a
cycle from each of the four direct configurations, and its length is the accepted
one the configuration's own side condition names.  The selected object avoids
every accepted length.  Registering the collision as `Incompatible` is what lets
the framework close the arm the moment the branch test takes it, with the closure
entry naming these two facts and nothing else.

The packing validity the two-window construction needs is the configuration's own
first component, read back rather than recomputed. -/
noncomputable instance instIncompatibleDirectCycle :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .typeBDirectCycle) where
  contradiction := fun _residual selected configuration => by
    obtain ⟨packing, valid, _maximal, _component, _present, _charge, _positive,
      _centre, _member, _high, present⟩ := configuration.down
    exact selected.down.1
      (Graph.TypeBDirectCycle.hasCycleWithLength_of_directCycleConfiguration
        valid present)

/-- **The terminal `[37]` is uninhabited**, at the spine's own key.

`not_contextDefect` is the mathematics: an admissible rank quotient is
target-complete, so no pair it identifies is separated by a boundary-degree
profile or by an outside context.  Registering it as `Impossible` is what lets
the framework close the arm the moment the branch test takes it, with the
closure entry naming this fact and nothing else. -/
noncomputable instance instImpossibleContextDefect :
    Impossible (Input BranchState Presentation presentation data)
      (K .contextDefect) where
  contradiction := fun residual value =>
    not_contextDefect (data := data) residual.object value.down

/-- **The node-`[54]` terminal is uninhabited**, at the spine's own keys.

`lem:p13-window-package`'s separated arm realizes the joint window, remainder and
forced-curvature package inside the labelled skeletons of the object's own order
and edge count — `lem:skeleton-dominates` at `𝒢_{n,m}`.  Node `[53]`'s yes arm
says that package demands strictly more states than there are such skeletons.
The two cannot both hold, and that is `prop:entropy-high-theta`: the entropy cap
closes the branch.

Everything past the two committed facts is
`PackedWindowRealization.SeparatedFamily.card_state_pi_le_skeletonBudget`. -/
noncomputable instance instIncompatibleEntropyCap :
    Incompatible (Input BranchState Presentation presentation data)
      (K .windowPackageSeparated) (K .entropyCapActive) where
  contradiction := fun residual package active => by
    classical
    obtain ⟨packing, valid, _attains⟩ :=
      residual.object.exists_windowPacking_card_eq data.windowOrder
    obtain ⟨coordinateCount, family, _windowBound, jointBound, slotsFit,
      poolRoom, _targetPackage, _deficitBound⟩ := package.down packing valid
    have capped :=
      family.card_state_pi_le_skeletonBudget residual.object.edgeCount
        slotsFit poolRoom
    have overflowLt : Graph.skeletonBudget residual.object <
        jointPackageDemand data residual.object packing := active.down packing valid
    rw [Graph.skeletonBudget] at overflowLt
    omega

/-- **The node-`[23]` terminal is uninhabited**, at the spine's own keys.

The same realization carries the window package on its own.  Node `[22]`'s
overflow arm says it demands strictly more states than there are skeletons of the
object's order and edge count, and `lem:skeleton-dominates` at `𝒢_{n,m}` says it
does not.  That is the manuscript's window-entropy overflow terminal. -/
noncomputable instance instIncompatibleWindowPackage :
    Incompatible (Input BranchState Presentation presentation data)
      (K .windowPackageSeparated) (K .barrierOverflow) where
  contradiction := fun residual package overflow => by
    classical
    obtain ⟨packing, valid, _attains⟩ :=
      residual.object.exists_windowPacking_card_eq data.windowOrder
    obtain ⟨coordinateCount, family, windowBound, _jointBound, slotsFit,
      poolRoom, _targetPackage, _deficitBound⟩ := package.down packing valid
    have capped :=
      family.card_state_pi_le_skeletonBudget residual.object.edgeCount
        slotsFit poolRoom
    have overflowLt : Graph.skeletonBudget residual.object <
        2 ^ (data.windowRate *
          data.separatedScaleCount residual.object.vertexCount *
          residual.object.windowPackingNumber data.windowOrder) := overflow.down
    rw [Graph.skeletonBudget] at overflowLt
    omega

/-- The key index at the full-rank residual of node `[34]`, Residual B.  This
is the index nodes `[47]` onwards extend; it is no longer an exit of the run. -/
abbrev completedKeys : FactKeys (Input BranchState Presentation presentation data) :=
  [K .curvatureFullRank, K .curvatureTargetRank, K .wedgeSupply,
    K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
    K .remainderNormalized, K .densityCap, K .barrierCap,
    K .windowPackageSeparated, K .surplusAtOrBelow,
    K .localAlgebra, K .maximalPacking, K .uncompressible, K .tightEndpoint,
    K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
    K .selection]

/-- The key index of a ledger that left the block at node `[32]`, into Branch
D.  It differs from the completed index in exactly one entry: the arm that was
taken.  A consumer of this exit cannot read the full-rank alternative, because
that key is not in its type. -/
abbrev curvatureRankDropKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .curvatureRankDrop, K .curvatureTargetRank, K .wedgeSupply,
    K .curvatureDemandFloor, K .boundaryDemand, K .stubSupply,
    K .remainderNormalized, K .densityCap, K .barrierCap,
    K .windowPackageSeparated, K .surplusAtOrBelow,
    K .localAlgebra, K .maximalPacking, K .uncompressible, K .tightEndpoint,
    K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
    K .selection]

/-- The key index after node `[35]`: the rank-drop exit with Branch D's
determination certificate appended. -/
abbrev branchDependenceKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .branchDependence :: curvatureRankDropKeys

/-- The key index of Branch D's surviving arm at node `[36]`: the
context-universal determination node `[38]` is stated on. -/
abbrev contextUniversalKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .contextUniversal :: branchDependenceKeys

/-- The key index of the closed terminal `[37]`: the target-defective quotient,
followed by the residual domain's distinguished closure key. -/
abbrev contextDefectKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .contextDefect :: branchDependenceKeys

/-! ### The indices nodes `[47]`--`[64]` build on the full-rank residual -/

/-- Node `[48]`: the forced curvature cost, on Residual B. -/
abbrev forcedCurvatureCostKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .forcedCurvatureCost :: completedKeys

/-- Node `[51]`: the high-entropy arm of the node-`[50]` split. -/
abbrev remainderEntropyHighKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .remainderEntropyHigh :: forcedCurvatureCostKeys

/-- Node `[52]`: window plus remainder accounting on the high-entropy arm. -/
abbrev entropyPackageKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .entropyPackageDemand :: remainderEntropyHighKeys

/-- Node `[50]`'s low-entropy arm. -/
abbrev remainderEntropyLowKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .remainderEntropyLow :: forcedCurvatureCostKeys

/-- The one dependent Residual C index.  `known` is the literal branch
prefix; no sibling prefix is coerced to another. -/
abbrev residualCKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .largeBudgetResidual :: known

/-- The paper's sufficiently-large regime, committed by the exhaustive order
split before the net-charge cap is activated. -/
abbrev residualCNetChargeLargeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .netChargeLarge :: residualCKeys known

/-- The paper's eventual net-cap conclusion appended to the literal Residual C
prefix.  Its sufficiently-large premise remains inside the fact. -/
abbrev residualCNetChargeCapKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .netChargeCap :: residualCNetChargeLargeKeys known

/-- Node `[53]`'s yes arm on the high-entropy package, closed at `[54]`. -/
abbrev entropyCapActiveKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .entropyCapActive :: entropyPackageKeys

/-- Node `[53]`'s no arm on the high-entropy package.  It retains the package
fact and enters the large-budget continuation. -/
abbrev entropyPackageLargeBudgetKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .largeBudgetResidual :: entropyPackageKeys

/-- The same exact budget comparison on the low-entropy arm, when its active
side is already incompatible with the separated realization. -/
abbrev lowEntropyCapActiveKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .entropyCapActive :: remainderEntropyLowKeys

/-- Node `[55]`, Residual C: node `[53]`'s no arm. -/
abbrev largeBudgetKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .largeBudgetResidual :: remainderEntropyLowKeys

/-- The exact net-charge continuation over an arbitrary Residual C tail. -/
abbrev residualCNetChargeLocalizationKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .netChargeLocalization :: residualCNetChargeCapKeys known

/-- The no-negative-support complement, carrying the paper's exact
window-join-pressure inequality and every incoming fact. -/
abbrev residualCWindowJoinPressureKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .windowJoinPressure :: K .netChargeNonNegative ::
    residualCNetChargeLocalizationKeys known

/-- The negative-support arm, carrying the selected connected support and every
incoming fact. -/
abbrev residualCNegativeSupportKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .negativeSupport :: K .netChargeNegative ::
    residualCNetChargeLocalizationKeys known

/-- Node `[60]`: the eventual cap and the nonnegative sign arm are
incompatible at a maximal packing. -/
noncomputable instance instIncompatibleNetChargeCapNonNegative :
    Incompatible (Input BranchState Presentation presentation data)
      (K .netChargeCap) (K .netChargeNonNegative) where
  contradiction := fun input cap nonNegative => by
    obtain ⟨packing, valid, cardinality⟩ :=
      input.object.exists_windowPacking_card_eq data.windowOrder
    have maximal : ∀ window : Finset input.object.Vertex,
        input.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member :=
      fun window windowInduces =>
        input.object.exists_mem_not_disjoint_of_card_eq data.windowOrder_pos
          valid cardinality windowInduces
    exact Nat.not_lt_of_ge (nonNegative.down packing valid maximal)
      (cap.down packing valid cardinality)

/-- The exhaustive result of consuming one arbitrary Residual C ledger.  Node
`[60]` has no constructor: only its negative arm reaches node `[61]`. -/
inductive ResidualCResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | negativeSupport
      (history : ExactLedger
        (Input BranchState Presentation presentation data) selected
        (residualCNegativeSupportKeys known))

/-- Nodes `[56]`--`[61]`, over the literal incoming Residual C ledger.

The sign decision is exhaustive at every finite order.  Its negative arm is
localized to a connected support.  The nonnegative arm contradicts the exact
net-cap theorem at the canonical maximum packing and is eliminated.  Before
that decision the one ledger is extended by the sufficiently-large routing
fact and then the unconditional net-cap fact valid on that branch. -/
noncomputable def runResidualC
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger
      (Input BranchState Presentation presentation data) current
      (residualCKeys known))
    (sufficientlyLarge :
      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate
        data.spineScale current.object.vertexCount)
    (densityCapPresent :
      FactKeys.Has (K (data := data) .densityCap) (residualCKeys known))
    (stubSupplyPresent :
      FactKeys.Has (K (data := data) .stubSupply) (residualCKeys known))
    (largeFresh : K (data := data) .netChargeLarge ∉ known)
    (smallFresh : K (data := data) .netChargeSmall ∉ known)
    (capFresh : K (data := data) .netChargeCap ∉ known)
    (localizationFresh : K (data := data) .netChargeLocalization ∉ known)
    (nonNegativeFresh : K (data := data) .netChargeNonNegative ∉ known)
    (negativeFresh : K (data := data) .netChargeNegative ∉ known)
    (closedFresh : closed ∉ known)
    (supportFresh : K (data := data) .negativeSupport ∉ known) :
    ResidualCResult current known := by
  classical
  letI := densityCapPresent
  letI := stubSupplyPresent
  match netChargeOrderDichotomy history (K .netChargeLarge) (K .netChargeSmall)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [residualCKeys, largeFresh])
      (by simp [residualCKeys, smallFresh]) with
  | .right smallHistory =>
      exact ((smallHistory.get (K .netChargeSmall)).down sufficientlyLarge).elim
  | .left largeHistory =>
      have capped :=
        (netChargeCap (data := data)).run largeHistory
          (by simp [residualCKeys, capFresh])
      have localized :=
        (netChargeLocalization (data := data)).run capped
          (by simp [residualCKeys, localizationFresh])
      match netChargeDichotomy localized (K .netChargeNonNegative)
          (K .netChargeNegative) (fun value => ⟨value⟩)
          (fun value => ⟨value⟩)
          (by simp [residualCKeys, nonNegativeFresh])
          (by simp [residualCKeys, negativeFresh]) with
      | .left nonNegativeHistory =>
          have closedHistory :=
            closeIncompatible nonNegativeHistory (K .netChargeCap)
              (K .netChargeNonNegative) (by simp [residualCKeys, closedFresh])
          have impossible : False := by
            apply ExactLedger.elimClosed
              (system := factSystem BranchState Presentation presentation data)
              closedHistory
            rw [closureKey_eq_closed]
            infer_instance
          exact impossible.elim
      | .right negativeHistory =>
          exact .negativeSupport
            ((negativeSupport (data := data)).run negativeHistory
              (by simp [residualCKeys, supportFresh]))

/-- Node `[62]`'s Type A arm over the literal Residual C ancestry. -/
abbrev residualCTypeALowSurplusKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeALowSurplus :: residualCNegativeSupportKeys known

/-- Node `[62]`'s Type B arm over the literal Residual C ancestry. -/
abbrev residualCTypeBHighSurplusKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHighSurplus :: residualCNegativeSupportKeys known

abbrev residualCTypeAReceiverRoutingKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAReceiverRouting :: residualCTypeALowSurplusKeys known

abbrev residualCTypeASaturatedReceiverKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedReceiver :: residualCTypeAReceiverRoutingKeys known

abbrev residualCTypeAPortReturnKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAPortReturn :: residualCTypeASaturatedReceiverKeys known

abbrev residualCTypeAVisibleEntryKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAVisibleEntryClause :: K .typeAVisibleEntry ::
    residualCTypeAPortReturnKeys known

abbrev residualCTypeAVisibleFirstExcessKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAVisibleFirstExcess :: residualCTypeAPortReturnKeys known

abbrev residualCTypeAUnsaturatedReceiverKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAUnsaturatedReceivers :: residualCTypeAReceiverRoutingKeys known

abbrev residualCTypeAUnsaturatedDischargeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAUnsaturatedDischarge ::
    residualCTypeAUnsaturatedReceiverKeys known

abbrev residualCTypeAUnsaturatedClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: residualCTypeAUnsaturatedDischargeKeys known

abbrev residualCTypeBNormalFormKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .highCentreNormalForm :: residualCTypeBHighSurplusKeys known

abbrev residualCTypeBHeavyCentreKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHeavyCentre :: residualCTypeBNormalFormKeys known

abbrev residualCTypeBLocalDichotomyKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBLocalDichotomy :: residualCTypeBHeavyCentreKeys known

abbrev residualCTypeBHeavyFanCapKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateCap :: residualCTypeBLocalDichotomyKeys known

abbrev residualCTypeBDegreeFourKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDegreeFourCentres :: residualCTypeBNormalFormKeys known

abbrev residualCTypeBDegreeFourFanCapKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateCap :: residualCTypeBDegreeFourKeys known

abbrev residualCTypeBDegreeFourProfileKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDegreeFourProfile :: residualCTypeBDegreeFourFanCapKeys known

/-- The already-ported Type A/Type B continuation currently instantiates the
generic index at the low-entropy cursor; no fact is reconstructed or dropped. -/
abbrev netChargeLocalizationKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCNetChargeLocalizationKeys remainderEntropyLowKeys

abbrev negativeSupportKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCNegativeSupportKeys remainderEntropyLowKeys

/-- Node `[63]`, Type A. -/
abbrev typeALowSurplusKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeALowSurplusKeys remainderEntropyLowKeys

/-- Node `[88]`: the routing and threshold algebra, on the Type A residual. -/
abbrev typeAReceiverRoutingKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeAReceiverRoutingKeys remainderEntropyLowKeys

/-- Node `[89]`, yes arm — the entry of node `[93]`. -/
abbrev typeASaturatedReceiverKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeASaturatedReceiverKeys remainderEntropyLowKeys

/-- `lem:typeA-port-return`, committed on the shared prefix of nodes `[93]`
and `[94]`: every completion port of the object carries an anchored return. -/
abbrev typeAPortReturnKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeAPortReturnKeys remainderEntropyLowKeys

/-- Node `[93]`, yes arm — the selected visible package and its compiled
response/germ prefix, at the entry of exits `(1)`--`(3)`. -/
abbrev typeAVisibleEntryKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeAVisibleEntryKeys remainderEntropyLowKeys

/-- Node `[93]`, no arm — node `[94]`, the selected visible-first silent
excess residual.  No `[101]+` key is appended before its missing routing
theorem is implemented. -/
abbrev typeAVisibleFirstExcessKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeAVisibleFirstExcessKeys remainderEntropyLowKeys

/-- Node `[89]`, no arm — node `[90]`. -/
abbrev typeAUnsaturatedReceiverKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeAUnsaturatedReceiverKeys remainderEntropyLowKeys

/-- Node `[64]`, Type B. -/
abbrev typeBHighSurplusKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBHighSurplusKeys remainderEntropyLowKeys

/-- Node `[68]`'s standing law, on the Type B residual. -/
abbrev typeBNormalFormKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBNormalFormKeys remainderEntropyLowKeys

/-- Node `[68]`, yes arm — the entry of node `[69]`. -/
abbrev typeBHeavyCentreKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBHeavyCentreKeys remainderEntropyLowKeys

/-- Node `[69]`: the heavy-centre local dichotomy, on that arm. -/
abbrev typeBLocalDichotomyKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBLocalDichotomyKeys remainderEntropyLowKeys

/-- Node `[70]` on the heavy arm, after `[69]`. -/
abbrev typeBHeavyFanCapKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBHeavyFanCapKeys remainderEntropyLowKeys


/-- Node `[68]`, no arm — the entry of node `[78]`. -/
abbrev typeBDegreeFourKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBDegreeFourKeys remainderEntropyLowKeys
/-- Node `[70]` on the degree-four arm, after `[78]`'s entry. -/
abbrev typeBDegreeFourFanCapKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBDegreeFourFanCapKeys remainderEntropyLowKeys

/-- Nodes `[78]`--`[79]`: the degree-four fan profile, on that arm. -/
abbrev typeBDegreeFourProfileKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBDegreeFourProfileKeys remainderEntropyLowKeys

/-! ### The Type B fan ledger `[71]`--`[76]` / `[80]`--`[85]`, as one walk

`prop:fan-closed-port-typeB-routing`, `cor:compatible-pair-typeB-routing` and
`prop:triangular-port-typeB-routing` all enter the local Type B fan ledger at
node `[72]`, and the manuscript walks `[80]`--`[85]` as *the same* ledger after
the degree-four cursor.  The indices below are that walk over whatever index its
entry cursor carries, so there is one spelling of each stage. -/

/-- `[71]`/`[80]`, yes: every assigned Type B centre is certificate-marked. -/
abbrev fanMarkedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateMarked :: known

/-- `[71]`/`[80]`, no: a fan-certificate residual centre exists. -/
abbrev fanCertResidualKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateResidual :: known

/-- `[75]`/`[84]` on a fan-certificate residual cursor. -/
abbrev fanCertResidualMassKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBBridgeMass :: fanCertResidualKeys known

/-- `[72]`/`[81]`, first half, closing arm. -/
abbrev fanDirectCycleClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeBDirectCycle :: known

/-- `[72]`/`[81]`, first half, surviving arm. -/
abbrev fanDirectCycleFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDirectCycleFree :: known

/-- `[72]`/`[81]`, second half, yes — the entry of `[74]`/`[82]`. -/
abbrev fanB2ChoiceKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBB2Choice :: fanDirectCycleFreeKeys known

/-- `[74]`/`[82]`: the hybrid B1 fan ledger. -/
abbrev fanHybridEntryKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHybridEntry :: fanB2ChoiceKeys known

/-- `[76]`/`[85]`: the exact post-ledger disjoint component fact. -/
abbrev fanDisjointLedgerKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDisjointLedger :: fanHybridEntryKeys known

/-- `[72]`/`[81]`, second half, no — the entry of `[73]`/`[83]`. -/
abbrev fanOverlapObstructionKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBOverlapObstruction :: fanDirectCycleFreeKeys known

/-- `[75]`/`[84]` on an overlap-obstruction cursor. -/
abbrev fanOverlapObstructionMassKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBBridgeMass :: fanOverlapObstructionKeys known

abbrev residualCTypeBCertificateMarkedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanMarkedKeys (residualCTypeBHeavyFanCapKeys known)

abbrev residualCTypeBDirectCycleClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanDirectCycleClosedKeys (residualCTypeBCertificateMarkedKeys known)

abbrev residualCTypeBDisjointLedgerKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanDisjointLedgerKeys (residualCTypeBCertificateMarkedKeys known)

abbrev residualCTypeBCertificateResidualKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanCertResidualKeys (residualCTypeBHeavyFanCapKeys known)

abbrev residualCTypeBCertificateResidualMassKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanCertResidualMassKeys (residualCTypeBHeavyFanCapKeys known)

abbrev residualCTypeBOverlapObstructionKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanOverlapObstructionKeys (residualCTypeBCertificateMarkedKeys known)

abbrev residualCTypeBOverlapObstructionMassKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanOverlapObstructionMassKeys (residualCTypeBCertificateMarkedKeys known)

abbrev residualCDegreeFourMarkedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanMarkedKeys (residualCTypeBDegreeFourProfileKeys known)

abbrev residualCDegreeFourDirectCycleClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanDirectCycleClosedKeys (residualCDegreeFourMarkedKeys known)

abbrev residualCDegreeFourDisjointLedgerKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanDisjointLedgerKeys (residualCDegreeFourMarkedKeys known)

abbrev residualCDegreeFourCertificateResidualKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanCertResidualKeys (residualCTypeBDegreeFourProfileKeys known)

abbrev residualCDegreeFourResidualMassKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanCertResidualMassKeys (residualCTypeBDegreeFourProfileKeys known)

abbrev residualCDegreeFourOverlapObstructionKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanOverlapObstructionKeys (residualCDegreeFourMarkedKeys known)

abbrev residualCDegreeFourOverlapObstructionMassKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanOverlapObstructionMassKeys (residualCDegreeFourMarkedKeys known)

/-- Node `[80]`, yes arm: the same certificate question at its second position. -/
abbrev degreeFourMarkedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourMarkedKeys remainderEntropyLowKeys

/-- Node `[81]`'s first half, closing arm. -/
abbrev degreeFourDirectCycleClosedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanDirectCycleClosedKeys degreeFourMarkedKeys

/-- Node `[81]`'s first half, surviving arm. -/
abbrev degreeFourDirectCycleFreeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanDirectCycleFreeKeys degreeFourMarkedKeys

/-- Node `[81]`, yes arm — the entry of `[82]`. -/
abbrev degreeFourB2ChoiceKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanB2ChoiceKeys degreeFourMarkedKeys

/-- Node `[82]`: the same hybrid ledger row, on the degree-four B2 cursor. -/
abbrev degreeFourHybridEntryKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanHybridEntryKeys degreeFourMarkedKeys

/-- Node `[81]`, no arm — the local entry of `[83]`, routed to `[84]`. -/
abbrev degreeFourLocalOverlapObstructionKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanOverlapObstructionKeys degreeFourMarkedKeys

/-- Node `[71]`, yes arm: every assigned Type B centre is certificate-marked. -/
abbrev typeBCertificateMarkedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBCertificateMarkedKeys remainderEntropyLowKeys

/-- Node `[72]`, the closing arm: an assigned centre carries one of the four
direct fan-window configurations, so the branch collides with the selection's own
avoidance and the closure entry is appended. -/
abbrev typeBDirectCycleClosedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBDirectCycleClosedKeys remainderEntropyLowKeys

/-- Node `[72]`, the surviving arm: every closed fan-window pair is
direct-cycle-free, so the local fan-window ledger is complete. -/
abbrev typeBDirectCycleFreeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanDirectCycleFreeKeys typeBCertificateMarkedKeys

/-- Node `[72]`/`[81]`, yes arm — the entry of `[74]`/`[82]`. -/
abbrev typeBB2ChoiceKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanB2ChoiceKeys typeBCertificateMarkedKeys

/-- Node `[74]`: the hybrid B1 fan ledger, on the heavy arm's B2 cursor. -/
abbrev typeBHybridEntryKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  fanHybridEntryKeys typeBCertificateMarkedKeys

/-- Node `[76]`: exact disjoint post-ledger components, after `[74]`. -/
abbrev typeBDisjointLedgerKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBDisjointLedgerKeys remainderEntropyLowKeys

/-- Node `[85]`: exact disjoint post-ledger components, after `[82]`. -/
abbrev degreeFourDisjointLedgerKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourDisjointLedgerKeys remainderEntropyLowKeys

/-- Node `[71]`, no arm: a fan-certificate residual centre exists. -/
abbrev typeBCertificateResidualKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBCertificateResidualKeys remainderEntropyLowKeys

/-- Node `[75]`: fan-mass estimate on the heavy certificate-residual cursor. -/
abbrev typeBCertificateResidualMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBCertificateResidualMassKeys remainderEntropyLowKeys

/-- Node `[80]`, no arm: a fan-certificate residual centre exists. -/
abbrev degreeFourCertificateResidualKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourCertificateResidualKeys remainderEntropyLowKeys

/-- Node `[84]`: fan-mass estimate on the degree-four certificate-residual cursor. -/
abbrev degreeFourResidualMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourResidualMassKeys remainderEntropyLowKeys

/-- Node `[72]`/`[81]`, no arm: the selected support carries a minimal overlap
obstruction. -/
abbrev typeBOverlapObstructionKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBOverlapObstructionKeys remainderEntropyLowKeys

/-- Node `[75]` entered from `[73]`: fan-mass estimate on the heavy overlap cursor. -/
abbrev typeBOverlapObstructionMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBOverlapObstructionMassKeys remainderEntropyLowKeys

abbrev degreeFourOverlapObstructionKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourOverlapObstructionKeys remainderEntropyLowKeys

/-- Node `[84]` entered from `[83]`: fan-mass estimate on the degree-four overlap cursor. -/
abbrev degreeFourOverlapObstructionMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourOverlapObstructionMassKeys remainderEntropyLowKeys

/-- The key index of the closed terminal `[39]`, proper atom compression. -/
abbrev atomCompressionKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .atomCompression :: contextUniversalKeys

/-- The key index after node `[40]`: the determination needs an enlarged
connected support. -/
abbrev delocalizedSupportKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .delocalizedSupport :: contextUniversalKeys

/-- The key index of the closed terminal `[42]`, proper-support smearing. -/
abbrev properDelocalizationKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .properDelocalization :: delocalizedSupportKeys

/-- The key index of the closed terminal `[46]`: whole-graph delocalization,
the repair identity, the global barrier, and the closure that barrier forces. -/
abbrev rankDropClosedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .repairIdentity :: K .globalBarrier ::
    K .globalDelocalization :: delocalizedSupportKeys

/-- The key index of a ledger that left the block at nodes `[21]`--`[22]` with
colliding package coordinates: the `O(1)` the manuscript's scale count
discards. -/
abbrev windowPackageCollidedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .windowPackageCollided, K .surplusAtOrBelow, K .localAlgebra,
    K .maximalPacking, K .uncompressible, K .tightEndpoint,
    K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
    K .selection]

/-- The key index of a ledger that left the block at node `[19]`. -/
abbrev surplusAboveKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .surplusAbove, K .localAlgebra, K .maximalPacking, K .uncompressible,
    K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
    K .returnAvoidance, K .selection]

/-- The key index of a ledger that left the block at node `[21]`. -/
abbrev barrierOverflowKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: [K .barrierOverflow, K .windowPackageSeparated,
    K .surplusAtOrBelow, K .localAlgebra,
    K .maximalPacking, K .uncompressible, K .tightEndpoint,
    K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
    K .selection]

/-! ## The local Type B fan ledger, `[71]`--`[76]` and `[80]`--`[85]`

One walk, run at whichever cursor enters it: `Decision`s and `AtomicCT`s carry
no predecessor, so a second entry re-registers nothing.  The heavy arm and the
degree-four arm were two inline copies of it inside `run`, differing only in
which exit constructor each reached.

Only `selection` comes from outside.  `[70]`'s cap is `sourceFreeManifest` and
`[71]`'s certificate question is a `Decision` on a property of the selected
residual.

The local fan walk records only facts proved on the incoming residual.  The
certificate-residual and overlap-obstruction arms are immediately extended by
the fan-mass row on the same ledger; the direct-cycle arm closes; and the B2
success arm records the disjoint post-ledger component fact.
-/

/-- **The exits of the local Type B fan ledger.** -/
inductive TypeBFanLedgerResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  /-- `[75]`/`[84]`: a fan-certificate residual centre has its mass bound. -/
  | certificateResidualMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (fanCertResidualMassKeys known))
  /-- `[72]`/`[81]`: a direct fan-window cycle, which collides with the
  selection's own avoidance. -/
  | directCycleClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (fanDirectCycleClosedKeys (fanMarkedKeys known)))
  /-- `[76]`/`[85]`: B2(a)--(c) and post-ledger components on the same history. -/
  | disjointLedger
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (fanDisjointLedgerKeys (fanMarkedKeys known)))
  /-- `[75]`/`[84]`: a minimal overlap obstruction has its mass bound. -/
  | overlapObstructionMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (fanOverlapObstructionMassKeys (fanMarkedKeys known)))

/-- **The local Type B fan ledger, run.** -/
noncomputable def runTypeBFanLedger
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .fanCertificateCap) known]
    [FactKeys.Has (K (data := data) .typeBHighSurplus) known]
    [FactKeys.Has (K (data := data) .remainderNormalized) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (markedFresh : K (data := data) .fanCertificateMarked ∉ known)
    (certResidualFresh : K (data := data) .fanCertificateResidual ∉ known)
    (cycleFresh : K (data := data) .typeBDirectCycle ∉ known)
    (cycleFreeFresh : K (data := data) .typeBDirectCycleFree ∉ known)
    (b2ChoiceFresh : K (data := data) .typeBB2Choice ∉ known)
    (obstructionFresh : K (data := data) .typeBOverlapObstruction ∉ known)
    (hybridFresh : K (data := data) .typeBHybridEntry ∉ known)
    (disjointFresh : K (data := data) .typeBDisjointLedger ∉ known)
    (massFresh : K (data := data) .typeBBridgeMass ∉ known)
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    TypeBFanLedgerResult current known := by
  classical
  -- Node `[71]`/`[80]`: is a certificate labelling present?
  match fanCertificateDichotomy history (K .typeBHighSurplus)
      (K .fanCertificateMarked) (K .fanCertificateResidual)
      (fun fact => fact.down) (fun marked => ⟨marked⟩)
      (fun residual => ⟨residual⟩)
      (by simp [markedFresh]) (by simp [certResidualFresh]) with
  | .right certResidual =>
      exact .certificateResidualMass
        ((bridgeFanMass (data := data) (K .fanCertificateResidual) (by simp)).run
          certResidual (by simp [massFresh]))
  | .left marked =>
  -- Node `[72]`/`[81]`, first half: are the direct fan-window cycles present?
  match directCycleDichotomy marked (K .typeBDirectCycle)
      (K .typeBDirectCycleFree) (K .typeBHighSurplus)
      (fun fact => fact.down) (fun present => ⟨present⟩) (fun free => ⟨free⟩)
      (by simp [cycleFresh]) (by simp [cycleFreeFresh]) with
  | .left cycleHistory =>
      exact .directCycleClosed
        (closeIncompatible cycleHistory (K .selection) (K .typeBDirectCycle)
          (by simp [closureFresh]))
  | .right freeHistory =>
      -- Node `[72]`/`[81]`, second half: does the B2 disjoint ledger exist?
      match b2AssignmentDichotomy freeHistory (K .typeBB2Choice)
          (K .typeBOverlapObstruction) (K .typeBDirectCycleFree)
          (fun fact => fact.down) (fun ledger => ⟨ledger⟩)
          (fun obstruction => ⟨obstruction⟩)
          (by simp [b2ChoiceFresh]) (by simp [obstructionFresh]) with
      | .left ledgerHistory =>
          -- Node `[74]`/`[82]`, then the exact disjoint post-ledger fact.
          exact .disjointLedger
            ((disjointPostLedgerComponents (data := data)).run
              ((hybridEntry (data := data)).run ledgerHistory
                (by simp [hybridFresh]))
              (by simp [disjointFresh]))
      | .right obstructionHistory =>
          exact .overlapObstructionMass
            ((bridgeFanMass (data := data) (K .typeBOverlapObstruction)
                (by simp)).run
              obstructionHistory (by simp [massFresh]))

/-- The exact exits of the node-`[64]` Type B entry walk.  The heavy and
degree-four arms share `runTypeBFanLedger`; only their immutable prefixes
differ. -/
inductive TypeBEntryResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | directCycleClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBDirectCycleClosedKeys known))
  | disjointLedger
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBDisjointLedgerKeys known))
  | certificateResidualMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBCertificateResidualMassKeys known))
  | overlapObstructionMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBOverlapObstructionMassKeys known))
  | degreeFourResidualMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourResidualMassKeys known))
  | degreeFourDirectCycleClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourDirectCycleClosedKeys known))
  | degreeFourDisjointLedger
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourDisjointLedgerKeys known))
  | degreeFourOverlapObstructionMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourOverlapObstructionMassKeys known))

/-- Nodes `[65]`--`[85]`, entered from node `[64]` on the literal ledger. -/
noncomputable def runTypeBEntry
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .tightEndpoint) known]
    [FactKeys.Has (K (data := data) .remainderNormalized) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current (residualCTypeBHighSurplusKeys known))
    (normalFresh : K (data := data) .highCentreNormalForm ∉ known)
    (heavyFresh : K (data := data) .typeBHeavyCentre ∉ known)
    (degreeFourFresh : K (data := data) .typeBDegreeFourCentres ∉ known)
    (localFresh : K (data := data) .typeBLocalDichotomy ∉ known)
    (capFresh : K (data := data) .fanCertificateCap ∉ known)
    (profileFresh : K (data := data) .typeBDegreeFourProfile ∉ known)
    (markedFresh : K (data := data) .fanCertificateMarked ∉ known)
    (certResidualFresh : K (data := data) .fanCertificateResidual ∉ known)
    (cycleFresh : K (data := data) .typeBDirectCycle ∉ known)
    (cycleFreeFresh : K (data := data) .typeBDirectCycleFree ∉ known)
    (b2ChoiceFresh : K (data := data) .typeBB2Choice ∉ known)
    (obstructionFresh : K (data := data) .typeBOverlapObstruction ∉ known)
    (hybridFresh : K (data := data) .typeBHybridEntry ∉ known)
    (disjointFresh : K (data := data) .typeBDisjointLedger ∉ known)
    (massFresh : K (data := data) .typeBBridgeMass ∉ known)
    (closedFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    TypeBEntryResult current known := by
  classical
  have normal :=
    (highCentreNormalForm (data := data)).run history (by simp [normalFresh])
  match heavyCentreDichotomy normal (K .typeBHighSurplus)
      (K .typeBHeavyCentre) (K .typeBDegreeFourCentres)
      (fun fact => fact.down) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [heavyFresh]) (by simp [degreeFourFresh]) with
  | .left heavyHistory =>
      have capped :=
        (fanCertificateCap (data := data)).run
          ((heavyCentreLocalDichotomy (data := data)).run heavyHistory
            (by simp [localFresh]))
          (by simp [capFresh])
      match runTypeBFanLedger capped
          (markedFresh := by simp [markedFresh])
          (certResidualFresh := by simp [certResidualFresh])
          (cycleFresh := by simp [cycleFresh])
          (cycleFreeFresh := by simp [cycleFreeFresh])
          (b2ChoiceFresh := by simp [b2ChoiceFresh])
          (obstructionFresh := by simp [obstructionFresh])
          (hybridFresh := by simp [hybridFresh])
          (disjointFresh := by simp [disjointFresh])
          (massFresh := by simp [massFresh])
          (closureFresh := by simp [closedFresh]) with
      | .certificateResidualMass h => exact .certificateResidualMass h
      | .directCycleClosed h => exact .directCycleClosed h
      | .disjointLedger h => exact .disjointLedger h
      | .overlapObstructionMass h => exact .overlapObstructionMass h
  | .right degreeFourHistory =>
      have profiled :=
        (degreeFourProfile (data := data)).run
          ((fanCertificateCap (data := data)).run degreeFourHistory
            (by simp [capFresh]))
          (by simp [profileFresh])
      match runTypeBFanLedger profiled
          (markedFresh := by simp [markedFresh])
          (certResidualFresh := by simp [certResidualFresh])
          (cycleFresh := by simp [cycleFresh])
          (cycleFreeFresh := by simp [cycleFreeFresh])
          (b2ChoiceFresh := by simp [b2ChoiceFresh])
          (obstructionFresh := by simp [obstructionFresh])
          (hybridFresh := by simp [hybridFresh])
          (disjointFresh := by simp [disjointFresh])
          (massFresh := by simp [massFresh])
          (closureFresh := by simp [closedFresh]) with
      | .certificateResidualMass h => exact .degreeFourResidualMass h
      | .directCycleClosed h => exact .degreeFourDirectCycleClosed h
      | .disjointLedger h => exact .degreeFourDisjointLedger h
      | .overlapObstructionMass h => exact .degreeFourOverlapObstructionMass h

/-- **The exits of the entry spine.**

Each constructor carries the canonical ledger at the residual the block was
argued about, indexed by exactly the facts that branch established.  There is
no further constructor and no payload beside the ledger. -/
inductive Result (selected : Input BranchState Presentation presentation data)
    where
  | surplusAbove
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected surplusAboveKeys)
  | barrierOverflow
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected barrierOverflowKeys)
  | windowPackageCollided
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected windowPackageCollidedKeys)
  | contextDefect
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected contextDefectKeys)
  | atomCompression
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected atomCompressionKeys)
  | properDelocalization
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected properDelocalizationKeys)
  | rankDropClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected rankDropClosedKeys)
  | entropyCapActive
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected entropyCapActiveKeys)
  | typeAExitOneClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected
          (typeAExitOneClosedKeys (residualCTypeAVisibleEntryKeys known)))
  | typeAExitTwoClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitTwoClosedKeys
          (typeAExitOneFreeKeys (residualCTypeAVisibleEntryKeys known))))
  | typeAExitThreeClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitThreeClosedKeys
          (typeAExitTwoFreeKeys
            (typeAExitOneFreeKeys (residualCTypeAVisibleEntryKeys known)))))
  | typeAExitThreeFree
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitThreeFreeKeys
          (typeAExitTwoFreeKeys
            (typeAExitOneFreeKeys (residualCTypeAVisibleEntryKeys known)))))
  | typeAExitFour
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitFourKeys
          (typeAExitThreeFreeKeys
            (typeAExitTwoFreeKeys
              (typeAExitOneFreeKeys (residualCTypeAVisibleEntryKeys known))))))
  | typeAExitFourLoop
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitFourFiniteDescentKeys
          (typeAExitFourLoopKeys
            (typeAExitThreeFreeKeys
              (typeAExitTwoFreeKeys
                (typeAExitOneFreeKeys
                  (residualCTypeAVisibleEntryKeys known)))))))
  | typeASaturatedHandoffVisible
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeASaturatedHandoffVisibleKeys
          (typeAExitFourFiniteDescentKeys
            (typeAExitFourLoopKeys
              (typeAExitThreeFreeKeys
                (typeAExitTwoFreeKeys
                  (typeAExitOneFreeKeys
                  (residualCTypeAVisibleEntryKeys known))))))))
  | typeASaturatedHandoffSilent
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeASaturatedHandoffSilentKeys
          (typeAExitFourFiniteDescentKeys
            (typeAExitFourLoopKeys
              (typeAExitThreeFreeKeys
                (typeAExitTwoFreeKeys
                  (typeAExitOneFreeKeys
                    (residualCTypeAVisibleEntryKeys known))))))))
  | typeASaturatedVisibleExitFour
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeASaturatedHandoffExitFourKeys
          (typeASaturatedHandoffVisibleKeys
            (typeAExitFourFiniteDescentKeys
              (typeAExitFourLoopKeys
                (typeAExitThreeFreeKeys
                  (typeAExitTwoFreeKeys
                    (typeAExitOneFreeKeys
                      (residualCTypeAVisibleEntryKeys known)))))))))
  | typeASaturatedVisibleExitFourFree
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeASaturatedHandoffExitFourFreeKeys
          (typeASaturatedHandoffVisibleKeys
            (typeAExitFourFiniteDescentKeys
              (typeAExitFourLoopKeys
                (typeAExitThreeFreeKeys
                  (typeAExitTwoFreeKeys
                    (typeAExitOneFreeKeys
                      (residualCTypeAVisibleEntryKeys known)))))))))
  | typeASaturatedVisibleExitFiveClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (closed :: typeAExitFiveKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffVisibleKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known))))))))))
  | typeASaturatedVisibleExitSixProperClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (closed :: typeAExitSixProperKeys (typeAExitFiveFreeKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffVisibleKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known)))))))))))
  | typeASaturatedVisibleExitSixGlobalClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (closed :: typeAExitSixGlobalKeys (typeAExitFiveFreeKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffVisibleKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known)))))))))))
  | typeASaturatedVisibleExitSixFree
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitSixFreeKeys (typeAExitFiveFreeKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffVisibleKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known)))))))))))
  | typeASaturatedSilentExitFour
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeASaturatedHandoffExitFourKeys
          (typeASaturatedHandoffSilentKeys
            (typeAExitFourFiniteDescentKeys
              (typeAExitFourLoopKeys
                (typeAExitThreeFreeKeys
                  (typeAExitTwoFreeKeys
                    (typeAExitOneFreeKeys
                      (residualCTypeAVisibleEntryKeys known)))))))))
  | typeASaturatedSilentExitFourFree
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeASaturatedHandoffExitFourFreeKeys
          (typeASaturatedHandoffSilentKeys
            (typeAExitFourFiniteDescentKeys
              (typeAExitFourLoopKeys
                (typeAExitThreeFreeKeys
                  (typeAExitTwoFreeKeys
                    (typeAExitOneFreeKeys
                      (residualCTypeAVisibleEntryKeys known)))))))))
  | typeASaturatedSilentExitFiveClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (closed :: typeAExitFiveKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffSilentKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known))))))))))
  | typeASaturatedSilentExitSixProperClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (closed :: typeAExitSixProperKeys (typeAExitFiveFreeKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffSilentKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known)))))))))))
  | typeASaturatedSilentExitSixGlobalClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (closed :: typeAExitSixGlobalKeys (typeAExitFiveFreeKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffSilentKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known)))))))))))
  | typeASaturatedSilentExitSixFree
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitSixFreeKeys (typeAExitFiveFreeKeys
          (typeASaturatedHandoffExitFourFreeKeys
            (typeASaturatedHandoffSilentKeys
              (typeAExitFourFiniteDescentKeys
                (typeAExitFourLoopKeys
                  (typeAExitThreeFreeKeys
                    (typeAExitTwoFreeKeys
                      (typeAExitOneFreeKeys
                        (residualCTypeAVisibleEntryKeys known)))))))))))
  | typeAExitFourReceiverDischarged
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitFourReceiverDischargedKeys
          (typeAExitThreeFreeKeys
            (typeAExitTwoFreeKeys
              (typeAExitOneFreeKeys (residualCTypeAVisibleEntryKeys known))))))
  | typeAExitFourFree
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitFourFreeKeys
          (typeAExitThreeFreeKeys
            (typeAExitTwoFreeKeys
              (typeAExitOneFreeKeys (residualCTypeAVisibleEntryKeys known))))))
  | typeAVisibleFirstExcess
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeAVisibleFirstExcessKeys known))
  | typeAUnsaturatedClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeAUnsaturatedClosedKeys known))
  | typeBDirectCycleClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBDirectCycleClosedKeys known))
  | typeBDisjointLedger
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBDisjointLedgerKeys known))
  | typeBCertificateResidualMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBCertificateResidualMassKeys known))
  | typeBOverlapObstructionMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCTypeBOverlapObstructionMassKeys known))
  | degreeFourResidualMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourResidualMassKeys known))
  | degreeFourDirectCycleClosed
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourDirectCycleClosedKeys known))
  | degreeFourDisjointLedger
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourDisjointLedgerKeys known))
  | degreeFourOverlapObstructionMass
      {known : FactKeys (Input BranchState Presentation presentation data)}
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (residualCDegreeFourOverlapObstructionMassKeys known))

/-- Continue the node-`[61]` ledger through the paper's exhaustive node-`[62]`
split and the corresponding Type A or Type B entry sequence. -/
noncomputable def continueNegativeSupport
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .remainderNormalized) known]
    [FactKeys.Has (K (data := data) .tightEndpoint) known]
    [FactKeys.Has (K (data := data) .returnAvoidance) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current (residualCNegativeSupportKeys known))
    (typeAFresh : K (data := data) .typeALowSurplus ∉ known)
    (typeBFresh : K (data := data) .typeBHighSurplus ∉ known)
    (typeARoutingFresh : K (data := data) .typeAReceiverRouting ∉ known)
    (typeASaturatedFresh : K (data := data) .typeASaturatedReceiver ∉ known)
    (typeAUnsaturatedFresh : K (data := data) .typeAUnsaturatedReceivers ∉ known)
    (typeAUnsaturatedDischargeFresh :
      K (data := data) .typeAUnsaturatedDischarge ∉ known)
    (typeAReturnFresh : K (data := data) .typeAPortReturn ∉ known)
    (typeAVisibleFresh : K (data := data) .typeAVisibleEntry ∉ known)
    (typeAExcessFresh : K (data := data) .typeAVisibleFirstExcess ∉ known)
    (typeAClauseFresh : K (data := data) .typeAVisibleEntryClause ∉ known)
    (typeAExitOneReturnFresh :
      K (data := data) .typeAExitOneReturn ∉ known)
    (typeAExitOneFreeFresh : K (data := data) .typeAExitOneFree ∉ known)
    (typeAExitTwoThetaFresh : K (data := data) .typeAExitTwoTheta ∉ known)
    (typeAExitTwoFreeFresh : K (data := data) .typeAExitTwoFree ∉ known)
    (typeAExitThreeCollisionFresh :
      K (data := data) .typeAExitThreeCollision ∉ known)
    (typeAExitThreeFreeFresh : K (data := data) .typeAExitThreeFree ∉ known)
    (typeAExitFourFresh : K (data := data) .typeAExitFour ∉ known)
    (typeAExitFourPeeledFresh :
      K (data := data) .typeAExitFourPeeled ∉ known)
    (typeASaturatedExitEntryFresh :
      K (data := data) .typeASaturatedExitEntry ∉ known)
    (typeAExitFourFiniteDescentFresh :
      K (data := data) .typeAExitFourFiniteDescent ∉ known)
    (typeASaturatedHandoffVisibleFresh :
      K (data := data) .typeASaturatedHandoffVisible ∉ known)
    (typeASaturatedHandoffSilentFresh :
      K (data := data) .typeASaturatedHandoffSilent ∉ known)
    (typeASaturatedHandoffExitFourFresh :
      K (data := data) .typeASaturatedHandoffExitFour ∉ known)
    (typeASaturatedHandoffExitFourFreeFresh :
      K (data := data) .typeASaturatedHandoffExitFourFree ∉ known)
    (typeAExitFiveFresh : K (data := data) .typeAExitFive ∉ known)
    (typeAExitFiveFreeFresh : K (data := data) .typeAExitFiveFree ∉ known)
    (typeAExitSixFresh : K (data := data) .typeAExitSix ∉ known)
    (typeAExitSixFreeFresh : K (data := data) .typeAExitSixFree ∉ known)
    (typeAExitSixProperFresh :
      K (data := data) .typeAExitSixProper ∉ known)
    (typeAExitSixGlobalFresh :
      K (data := data) .typeAExitSixGlobal ∉ known)
    (typeAExitFourReceiverDischargedFresh :
      K (data := data) .typeAExitFourReceiverDischarged ∉ known)
    (typeAExitFourFreeFresh : K (data := data) .typeAExitFourFree ∉ known)
    (normalFresh : K (data := data) .highCentreNormalForm ∉ known)
    (heavyFresh : K (data := data) .typeBHeavyCentre ∉ known)
    (degreeFourFresh : K (data := data) .typeBDegreeFourCentres ∉ known)
    (localFresh : K (data := data) .typeBLocalDichotomy ∉ known)
    (capFresh : K (data := data) .fanCertificateCap ∉ known)
    (profileFresh : K (data := data) .typeBDegreeFourProfile ∉ known)
    (markedFresh : K (data := data) .fanCertificateMarked ∉ known)
    (certResidualFresh : K (data := data) .fanCertificateResidual ∉ known)
    (cycleFresh : K (data := data) .typeBDirectCycle ∉ known)
    (cycleFreeFresh : K (data := data) .typeBDirectCycleFree ∉ known)
    (b2ChoiceFresh : K (data := data) .typeBB2Choice ∉ known)
    (obstructionFresh : K (data := data) .typeBOverlapObstruction ∉ known)
    (hybridFresh : K (data := data) .typeBHybridEntry ∉ known)
    (disjointFresh : K (data := data) .typeBDisjointLedger ∉ known)
    (massFresh : K (data := data) .typeBBridgeMass ∉ known)
    (closedFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    Result current := by
  classical
  match typeSplitDichotomy history (K .negativeSupport)
      (K .typeALowSurplus) (K .typeBHighSurplus)
      (fun fact => fact.down) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [typeAFresh]) (by simp [typeBFresh]) with
  | .left typeAHistory =>
      have routed :=
        (typeAReceiverRouting (data := data)).run typeAHistory
          (by simp [typeARoutingFresh])
      match typeASaturationDichotomy routed (K .typeALowSurplus)
          (K .typeASaturatedReceiver) (K .typeAUnsaturatedReceivers)
          (fun fact => fact.down) (fun value => ⟨value⟩)
          (fun value => ⟨value⟩)
          (by simp [typeASaturatedFresh])
          (by simp [typeAUnsaturatedFresh]) with
      | .right unsaturatedHistory =>
          have discharged :=
            (typeAUnsaturatedDischarge (data := data)).run unsaturatedHistory
              (by simp [typeAUnsaturatedDischargeFresh])
          exact .typeAUnsaturatedClosed
            (closeIncompatible discharged (K .typeALowSurplus)
              (K .typeAUnsaturatedDischarge) (by simp [closedFresh]))
      | .left saturatedHistory =>
          have withReturn :=
            (typeAPortReturn (data := data)).run saturatedHistory
              (by simp [typeAReturnFresh])
          match typeAVisibleEntryDichotomy withReturn
              (K .typeAReceiverRouting) (K .typeASaturatedReceiver)
              (K .typeAVisibleEntry) (K .typeAVisibleFirstExcess)
              (fun fact => fact.down) (fun fact => fact.down)
              (fun value => ⟨value⟩) (fun value => ⟨value⟩)
              (by simp [typeAVisibleFresh])
              (by simp [typeAExcessFresh]) with
          | .left visibleHistory =>
              have packaged :=
                (typeAVisibleEntryClause (data := data)).run visibleHistory
                  (by simp [typeAClauseFresh])
              match runExitChain packaged
                  (by simp [typeAExitOneReturnFresh])
                  (by simp [typeAExitOneFreeFresh])
                  (by simp [typeAExitTwoThetaFresh])
                  (by simp [typeAExitTwoFreeFresh])
                  (by simp [typeAExitThreeCollisionFresh])
                  (by simp [typeAExitThreeFreeFresh])
                  (by simp [closedFresh]) with
              | .exitOneClosed h => exact .typeAExitOneClosed h
              | .exitTwoClosed h => exact .typeAExitTwoClosed h
              | .exitThreeClosed h => exact .typeAExitThreeClosed h
              | .free h =>
                  match typeAExitFour h
                      (by simp [typeAExitFourFresh])
                      (by simp [typeAExitFourFreeFresh]) with
                  | .left exitHistory =>
                      let peeledHistory :=
                        (typeAExitFourPeelingStep (data := data)).run
                          exitHistory (by simp [typeAExitFourPeeledFresh])
                      match typeAExitFourRetest peeledHistory
                          (by simp [typeASaturatedExitEntryFresh])
                          (by simp [typeAExitFourReceiverDischargedFresh]) with
                      | .left loopHistory =>
                          let descentHistory :=
                            (typeAExitFourFiniteDescent (data := data)).run
                              loopHistory
                              (by simp [typeAExitFourFiniteDescentFresh])
                          match typeASaturatedHandoffSplit descentHistory
                              (by simp [typeASaturatedHandoffVisibleFresh])
                              (by simp [typeASaturatedHandoffSilentFresh]) with
                          | .left visibleLoopHistory =>
                              match typeASaturatedHandoffVisibleExitFour
                                  visibleLoopHistory
                                  (by
                                    simp [typeASaturatedHandoffExitFourFresh])
                                  (by
                                    simp [typeASaturatedHandoffExitFourFreeFresh]) with
                              | .left exitHistory =>
                                  exact .typeASaturatedVisibleExitFour exitHistory
                              | .right freeHistory =>
                                  match typeAExitFive freeHistory
                                      (by simp [typeAExitFiveFresh])
                                      (by simp [typeAExitFiveFreeFresh]) with
                                  | .left exitFiveHistory =>
                                      exact .typeASaturatedVisibleExitFiveClosed
                                        (closeIncompatible exitFiveHistory
                                          (K .uncompressible)
                                          (K .typeAExitFive)
                                          (by simp [closedFresh]))
                                  | .right exitFiveFreeHistory =>
                                      match typeAExitSix exitFiveFreeHistory
                                          (by simp [typeAExitSixFresh])
                                          (by simp [typeAExitSixFreeFresh]) with
                                      | .left exitSixHistory =>
                                          match typeAExitSixScope exitSixHistory
                                              (by
                                                simp [typeAExitSixProperFresh])
                                              (by
                                                simp [typeAExitSixGlobalFresh]) with
                                          | .left properHistory =>
                                              exact
                                                .typeASaturatedVisibleExitSixProperClosed
                                                  (closeIncompatible
                                                    properHistory
                                                    (K .selection)
                                                    (K .typeAExitSixProper)
                                                    (by simp [closedFresh]))
                                          | .right globalHistory =>
                                              exact
                                                .typeASaturatedVisibleExitSixGlobalClosed
                                                  (closeIncompatible
                                                    globalHistory
                                                    (K .selection)
                                                    (K .typeAExitSixGlobal)
                                                    (by simp [closedFresh]))
                                      | .right exitSixFreeHistory =>
                                          exact .typeASaturatedVisibleExitSixFree
                                            exitSixFreeHistory
                          | .right silentLoopHistory =>
                              match typeASaturatedHandoffSilentExitFour
                                  silentLoopHistory
                                  (by
                                    simp [typeASaturatedHandoffExitFourFresh])
                                  (by
                                    simp [typeASaturatedHandoffExitFourFreeFresh]) with
                              | .left exitHistory =>
                                  exact .typeASaturatedSilentExitFour exitHistory
                              | .right freeHistory =>
                                  match typeAExitFive freeHistory
                                      (by simp [typeAExitFiveFresh])
                                      (by simp [typeAExitFiveFreeFresh]) with
                                  | .left exitFiveHistory =>
                                      exact .typeASaturatedSilentExitFiveClosed
                                        (closeIncompatible exitFiveHistory
                                          (K .uncompressible)
                                          (K .typeAExitFive)
                                          (by simp [closedFresh]))
                                  | .right exitFiveFreeHistory =>
                                      match typeAExitSix exitFiveFreeHistory
                                          (by simp [typeAExitSixFresh])
                                          (by simp [typeAExitSixFreeFresh]) with
                                      | .left exitSixHistory =>
                                          match typeAExitSixScope exitSixHistory
                                              (by
                                                simp [typeAExitSixProperFresh])
                                              (by
                                                simp [typeAExitSixGlobalFresh]) with
                                          | .left properHistory =>
                                              exact
                                                .typeASaturatedSilentExitSixProperClosed
                                                  (closeIncompatible
                                                    properHistory
                                                    (K .selection)
                                                    (K .typeAExitSixProper)
                                                    (by simp [closedFresh]))
                                          | .right globalHistory =>
                                              exact
                                                .typeASaturatedSilentExitSixGlobalClosed
                                                  (closeIncompatible
                                                    globalHistory
                                                    (K .selection)
                                                    (K .typeAExitSixGlobal)
                                                    (by simp [closedFresh]))
                                      | .right exitSixFreeHistory =>
                                          exact .typeASaturatedSilentExitSixFree
                                            exitSixFreeHistory
                      | .right dischargedHistory =>
                          exact .typeAExitFourReceiverDischarged
                            dischargedHistory
                  | .right freeHistory => exact .typeAExitFourFree freeHistory
          | .right excessHistory =>
              exact .typeAVisibleFirstExcess excessHistory
  | .right typeBHistory =>
      match runTypeBEntry typeBHistory normalFresh heavyFresh degreeFourFresh
          localFresh capFresh profileFresh markedFresh certResidualFresh
          cycleFresh cycleFreeFresh b2ChoiceFresh obstructionFresh hybridFresh
          disjointFresh massFresh closedFresh with
      | .directCycleClosed h => exact .typeBDirectCycleClosed h
      | .disjointLedger h => exact .typeBDisjointLedger h
      | .certificateResidualMass h => exact .typeBCertificateResidualMass h
      | .overlapObstructionMass h => exact .typeBOverlapObstructionMass h
      | .degreeFourResidualMass h => exact .degreeFourResidualMass h
      | .degreeFourDirectCycleClosed h => exact .degreeFourDirectCycleClosed h
      | .degreeFourDisjointLedger h => exact .degreeFourDisjointLedger h
      | .degreeFourOverlapObstructionMass h =>
          exact .degreeFourOverlapObstructionMass h

set_option maxHeartbeats 4000000 in
/-- **Block A, run.**

The fact-only rows are composed by `AtomicCT.run`, which appends each row's
declared productions to the incoming index; the three diamonds are composed by
`Decision.run`, which commits the arm actually taken and leaves the other
arm's key out of this branch's index entirely.  The one uninhabited arm is
closed by `closeImpossible`, which appends Core's reserved closure key.

Every prerequisite is discharged by instance resolution against the incoming
index -- a row that asked for a fact the branch has not proved would not
elaborate -- and every freshness side condition is decided on the exact keys.
No row names a producer, a predecessor, or an execution position. -/
noncomputable def runCore
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (opened : OpenedScope
      (P := problem BranchState Presentation presentation data) (K .selection))
    (sufficientlyLarge :
      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate
        data.spineScale opened.selected.object.vertexCount) :
    Result opened.selected := by
  classical
  -- Nodes `[5]`--`[18]`: six fact-only rows against one immutable prefix.
  have afterReturn :=
    (returnAvoidance (data := data)).run opened.history (by simp)
  have afterProper :=
    (noProperBaseline (data := data)).run afterReturn (by simp)
  have afterCriticality :=
    (deletionCriticality (data := data)).run afterProper (by simp)
  have afterReplacement :=
    (interfaceReplacement T targetPredicate).run
      afterCriticality (by simp)
  have afterPacking :=
    (obstructionPacking (data := data)).run afterReplacement (by simp)
  have afterAlgebra := (localAlgebra (data := data)).run afterPacking (by simp)
  -- Node `[19]`: the surplus split.
  match surplusDichotomy afterAlgebra (K .surplusAbove) (K .surplusAtOrBelow)
      (fun above => ⟨above⟩) (fun atOrBelow => ⟨atOrBelow⟩)
      (by simp) (by simp) with
  | .left aboveHistory => exact .surplusAbove aboveHistory
  | .right belowHistory =>
      -- Nodes `[21]`--`[22]`: the selection of the window package.
      match windowPackageDichotomy belowHistory (K .windowPackageSeparated)
          (K .windowPackageCollided) (fun separated => ⟨separated⟩)
          (fun collided => ⟨collided⟩) (by simp) (by simp) with
      | .right collidedHistory => exact .windowPackageCollided collidedHistory
      | .left separatedHistory =>
      -- Node `[21]`: the finite barrier enumeration.
      match barrierEnumerationDichotomy separatedHistory (K .barrierCap)
          (K .barrierOverflow) (fun cap => ⟨cap⟩) (fun overflow => ⟨overflow⟩)
          (by simp) (by simp) with
      | .right overflowHistory =>
          -- Node `[23]`: the window-entropy overflow terminal, closed by the
          -- same realization.
          exact .barrierOverflow
            (closeIncompatible overflowHistory (K .windowPackageSeparated)
              (K .barrierOverflow) (by simp))
      | .left capHistory =>
          -- Nodes `[22]`--`[24]`: spend the retained cap.
          -- Nodes `[25]`--`[27]`: normalize the packed-window remainder.
          -- Nodes `[28]`--`[29]`: account for its boundary demand.
          -- Node `[30]`: the wedge lower bound, and the demand floor that
          -- substituting `[29]` into it produces.
          -- Node `[31]`: the curvature target-rank of the remainder.
          have afterRank :=
            (curvatureTargetRank (data := data)).run
              ((wedgeSupply (data := data)).run
                ((boundaryDemand (data := data)).run
                  ((remainderNormalization (data := data)).run
                    ((densityBudget (data := data)).run capHistory (by simp))
                    (by simp))
                  (by simp))
                (by simp))
              (by simp)
          -- Node `[32]`: the rank-drop decision.
          match curvatureRankDichotomy afterRank (K .curvatureTargetRank)
              (K .curvatureRankDrop) (K .curvatureFullRank)
              (fun fact => fact.down) (fun drop => ⟨drop⟩) (fun full => ⟨full⟩)
              (by simp) (by simp) with
          | .left dropHistory =>
              -- Nodes `[33]`/`[35]`: unpack the drop into Branch D's
              -- determination certificate.
              have afterBranch :=
                (branchDependence (data := data)).run dropHistory (by simp)
              -- Node `[36]`: the context-validity test.
              match contextValidityDichotomy afterBranch (K .contextDefect)
                  (K .contextUniversal) (fun defect => ⟨defect⟩)
                  (fun universal => ⟨universal⟩) (by simp) (by simp) with
              | .left defectHistory =>
                  -- Node `[37]`: the target-defective quotient.  An admissible
                  -- quotient cannot be one, so the arm closes here.
                  exact .contextDefect
                    (closeImpossible defectHistory (K .contextDefect) (by simp))
              | .right universalHistory =>
                  -- Node `[38]`: is the determination certified already at `C`?
                  match atomCompressionDichotomy universalHistory
                      (K .branchDependence) (K .contextUniversal)
                      (K .atomCompression) (K .delocalizedSupport)
                      (fun fact => fact.down) (fun fact => fact.down)
                      (fun compression => ⟨compression⟩)
                      (fun delocalized => ⟨delocalized⟩)
                      (by simp) (by simp) with
                  | .left compressionHistory =>
                      -- Node `[39]`: a target-complete compression of the
                      -- proper atom, forbidden by `cor:uncompressible`.
                      exact .atomCompression
                        (closeIncompatible compressionHistory (K .selection)
                          (K .atomCompression) (by simp))
                  | .right delocalizedHistory =>
                      -- Node `[41]`: is the enlarged support proper in `G`?
                      match delocalizationScopeDichotomy delocalizedHistory
                          (K .delocalizedSupport) (K .properDelocalization)
                          (K .globalDelocalization) (fun fact => fact.down)
                          (fun proper => ⟨proper⟩) (fun global => ⟨global⟩)
                          (by simp) (by simp) with
                      | .left properHistory =>
                          -- Node `[42]`: `lem:proper-smearing`.
                          exact .properDelocalization
                            (closeIncompatible properHistory (K .selection)
                              (K .properDelocalization) (by simp))
                      | .right globalHistory =>
                          -- Nodes `[43]`--`[45]`, then the terminal `[46]`:
                          -- `lem:no-silent-global-smearing`.
                          exact .rankDropClosed
                            (closeIncompatible
                              ((globalBarrier (data := data)).run globalHistory
                                (by simp))
                              (K .selection) (K .globalBarrier) (by simp))
          | .right fullHistory =>
              -- Nodes `[47]`--`[48]`: the forced curvature cost, on Residual B.
              have afterCost :=
                (forcedCurvatureCost (data := data)).run fullHistory (by simp)
              -- Nodes `[49]`--`[50]`: the per-vertex remainder entropy split.
              match remainderEntropyDichotomy afterCost
                  (K .remainderEntropyHigh) (K .remainderEntropyLow)
                  (fun high => ⟨high⟩) (fun low => ⟨low⟩)
                  (by simp) (by simp) with
              | .left highHistory =>
                  -- Nodes `[51]`--`[52]`: append the high-entropy package, then
                  -- consume it at the node-`[53]` comparison.  The yes arm is
                  -- the paper's closed node `[54]`; only the complementary
                  -- large-budget arm survives this phase boundary.
                  have packageHistory :=
                    (entropyPackage (data := data)).run highHistory (by simp)
                  match entropyCapDichotomy packageHistory (K .entropyCapActive)
                      (K .largeBudgetResidual) (fun active => ⟨active⟩)
                      (fun large => ⟨Or.inl large⟩) (by simp) (by simp) with
                  | .left activeHistory =>
                      exact .entropyCapActive
                        (closeIncompatible activeHistory
                          (K .windowPackageSeparated) (K .entropyCapActive)
                          (by simp))
                  | .right largeHistory =>
                      match runResidualC (known := entropyPackageKeys) largeHistory
                          (sufficientlyLarge := sufficientlyLarge)
                          (densityCapPresent := by infer_instance)
                          (stubSupplyPresent := by infer_instance)
                          (largeFresh := by simp)
                          (smallFresh := by simp)
                          (capFresh := by simp)
                          (localizationFresh := by simp)
                          (nonNegativeFresh := by simp)
                          (negativeFresh := by simp)
                          (closedFresh := by simp)
                          (supportFresh := by simp) with
                      | .negativeSupport supportHistory =>
                          exact continueNegativeSupport supportHistory
                            (typeAFresh := by simp) (typeBFresh := by simp)
                            (typeARoutingFresh := by simp)
                            (typeASaturatedFresh := by simp)
                            (typeAUnsaturatedFresh := by simp)
                            (typeAUnsaturatedDischargeFresh := by simp)
                            (typeAReturnFresh := by simp)
                            (typeAVisibleFresh := by simp)
                            (typeAExcessFresh := by simp)
                            (typeAClauseFresh := by simp)
                            (typeAExitOneReturnFresh := by simp)
                            (typeAExitOneFreeFresh := by simp)
                            (typeAExitTwoThetaFresh := by simp)
                            (typeAExitTwoFreeFresh := by simp)
                            (typeAExitThreeCollisionFresh := by simp)
                            (typeAExitThreeFreeFresh := by simp)
                            (typeAExitFourFresh := by simp)
                            (typeAExitFourPeeledFresh := by simp)
                            (typeASaturatedExitEntryFresh := by simp)
                            (typeAExitFourFiniteDescentFresh := by simp)
                            (typeASaturatedHandoffVisibleFresh := by simp)
                            (typeASaturatedHandoffSilentFresh := by simp)
                            (typeASaturatedHandoffExitFourFresh := by simp)
                            (typeASaturatedHandoffExitFourFreeFresh := by simp)
                            (typeAExitFiveFresh := by simp)
                            (typeAExitFiveFreeFresh := by simp)
                            (typeAExitSixFresh := by simp)
                            (typeAExitSixFreeFresh := by simp)
                            (typeAExitSixProperFresh := by simp)
                            (typeAExitSixGlobalFresh := by simp)
                            (typeAExitFourReceiverDischargedFresh := by simp)
                            (typeAExitFourFreeFresh := by simp)
                            (normalFresh := by simp) (heavyFresh := by simp)
                            (degreeFourFresh := by simp) (localFresh := by simp)
                            (capFresh := by simp) (profileFresh := by simp)
                            (markedFresh := by simp) (certResidualFresh := by simp)
                            (cycleFresh := by simp) (cycleFreeFresh := by simp)
                            (b2ChoiceFresh := by simp)
                            (obstructionFresh := by simp) (hybridFresh := by simp)
                            (disjointFresh := by simp)
                            (massFresh := by simp)
                            (closedFresh := by simp)
              | .right lowHistory =>
                  -- Every surviving low-entropy case has the same continuation
                  -- in `prop:two-budget`; no finite surrogate for the paper's
                  -- asymptotic local-type-vector condition is introduced.
                  have largeHistory :=
                    (lowEntropyLargeBudget (data := data)).run lowHistory
                      (by simp)
                  match runResidualC (known := remainderEntropyLowKeys) largeHistory
                      (sufficientlyLarge := sufficientlyLarge)
                      (densityCapPresent := by infer_instance)
                      (stubSupplyPresent := by infer_instance)
                      (largeFresh := by simp)
                      (smallFresh := by simp)
                      (capFresh := by simp)
                      (localizationFresh := by simp)
                      (nonNegativeFresh := by simp)
                      (negativeFresh := by simp)
                      (closedFresh := by simp)
                      (supportFresh := by simp) with
                  | .negativeSupport supportHistory =>
                      exact continueNegativeSupport supportHistory
                        (typeAFresh := by simp) (typeBFresh := by simp)
                        (typeARoutingFresh := by simp)
                        (typeASaturatedFresh := by simp)
                        (typeAUnsaturatedFresh := by simp)
                        (typeAUnsaturatedDischargeFresh := by simp)
                        (typeAReturnFresh := by simp)
                        (typeAVisibleFresh := by simp)
                        (typeAExcessFresh := by simp)
                        (typeAClauseFresh := by simp)
                        (typeAExitOneReturnFresh := by simp)
                        (typeAExitOneFreeFresh := by simp)
                        (typeAExitTwoThetaFresh := by simp)
                        (typeAExitTwoFreeFresh := by simp)
                        (typeAExitThreeCollisionFresh := by simp)
                        (typeAExitThreeFreeFresh := by simp)
                        (typeAExitFourFresh := by simp)
                        (typeAExitFourPeeledFresh := by simp)
                        (typeASaturatedExitEntryFresh := by simp)
                        (typeAExitFourFiniteDescentFresh := by simp)
                        (typeASaturatedHandoffVisibleFresh := by simp)
                        (typeASaturatedHandoffSilentFresh := by simp)
                        (typeASaturatedHandoffExitFourFresh := by simp)
                        (typeASaturatedHandoffExitFourFreeFresh := by simp)
                        (typeAExitFiveFresh := by simp)
                        (typeAExitFiveFreeFresh := by simp)
                        (typeAExitSixFresh := by simp)
                        (typeAExitSixFreeFresh := by simp)
                        (typeAExitSixProperFresh := by simp)
                        (typeAExitSixGlobalFresh := by simp)
                        (typeAExitFourReceiverDischargedFresh := by simp)
                        (typeAExitFourFreeFresh := by simp)
                        (normalFresh := by simp) (heavyFresh := by simp)
                        (degreeFourFresh := by simp) (localFresh := by simp)
                        (capFresh := by simp) (profileFresh := by simp)
                        (markedFresh := by simp) (certResidualFresh := by simp)
                        (cycleFresh := by simp) (cycleFreeFresh := by simp)
                        (b2ChoiceFresh := by simp)
                        (obstructionFresh := by simp) (hybridFresh := by simp)
                        (disjointFresh := by simp)
                        (massFresh := by simp)
                        (closedFresh := by simp)

/-! ## What the run leaves behind -/

/-- **The audit of a completed block is exactly its eighteen facts, in the
order they were committed.**

The audit reads the ledger's own key index, so this is the statement that the
block committed these eighteen and nothing else -- no closure entry, no
bookkeeping fact, no duplicate. -/
theorem complete_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected completedKeys) :
    (ExactLedger.audit history).facts =
      [(name .curvatureFullRank),
        (name .curvatureTargetRank),
        (name .wedgeSupply),
        (name .curvatureDemandFloor),
        (name .boundaryDemand),
        (name .stubSupply),
        (name .remainderNormalized),
        (name .densityCap),
        (name .barrierCap),
        (name .windowPackageSeparated),
        (name .surplusAtOrBelow),
        (name .localAlgebra),
        (name .maximalPacking),
        (name .uncompressible),
        (name .tightEndpoint),
        (name .slackIndependent),
        (name .noProperBaseline),
        (name .returnAvoidance),
        (name .selection)] := rfl

/-- **Every fact of a completed block is accounted for by a chronological
commit.**  Nothing was archived, rebased, or dropped along the way. -/
theorem complete_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected completedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-! ### The two Type exits of node `[62]`

Both carry everything the run proved from node `[1]` to node `[61]`, and differ
in exactly one entry: whether the selected connected negative support carries
assigned high-degree surplus.  Neither can read the other's arm, and neither can
read either arm of node `[59]` it did not take, of node `[53]`, of node `[50]`,
of node `[32]`, of node `[21]`, or of node `[19]`. -/

theorem typeALowSurplus_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeALowSurplusKeys) :
    (ExactLedger.audit history).facts =
      (name .typeALowSurplus) ::
        (name .negativeSupport) ::
        (name .netChargeNegative) ::
        (name .netChargeLocalization) ::
        (name .netChargeCap) ::
        (name .netChargeLarge) ::
        (name .largeBudgetResidual) ::
        (name .remainderEntropyLow) ::
        (name .forcedCurvatureCost) ::
        (name .curvatureFullRank) ::
        (name .curvatureTargetRank) ::
        (name .wedgeSupply) ::
        (name .curvatureDemandFloor) ::
        (name .boundaryDemand) ::
        (name .stubSupply) ::
        (name .remainderNormalized) ::
        (name .densityCap) ::
        (name .barrierCap) ::
        (name .windowPackageSeparated) ::
        (name .surplusAtOrBelow) ::
        (name .localAlgebra) ::
        (name .maximalPacking) ::
        (name .uncompressible) ::
        (name .tightEndpoint) ::
        (name .slackIndependent) ::
        (name .noProperBaseline) ::
        (name .returnAvoidance) ::
        [(name .selection)] := rfl

/-- **Every fact of the Type A residual is accounted for by a chronological
commit.**  The whole run -- eight further facts on top of the full-rank
residual, across two more decisions -- is one append-only history with nothing
archived, rebased, or dropped. -/
theorem typeALowSurplus_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeALowSurplusKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-! ### The two arms of node `[89]`

Node `[88]` commits the canonical receiver routing and the threshold algebra on
the Type A residual of `[63]`, and node `[89]` then splits on whether some
receiver has reached its threshold.  The two indices below differ in exactly
that one entry, and both carry the routing, which is what makes `L(w)` a
complete assignment on either arm.

Neither arm can read the other's, and neither can read either arm of node
`[62]`, `[59]`, `[53]`, `[50]`, `[32]`, `[21]` or `[19]` it did not take. -/

/-- **The visible-entry arm's audit is exactly its facts, in commit order.** -/
theorem typeAVisibleEntry_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleEntryKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The visible-first excess arm's audit is exactly its facts, in commit
order.** -/
theorem typeAVisibleFirstExcess_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleFirstExcessKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The unsaturated arm's audit is exactly its facts, in commit order.** -/
theorem typeAUnsaturatedReceivers_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAUnsaturatedReceiverKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The unsaturated arm commits the node-`[88]` routing and the node-`[90]`
capacity on top of the whole Type A history**, and nothing else: no closure
entry, no bookkeeping fact, no duplicate, and the saturated alternative is not
in this branch's index at all. -/
theorem typeAUnsaturatedReceivers_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAUnsaturatedReceiverKeys) :
    (ExactLedger.audit history).facts =
      (name .typeAUnsaturatedReceivers) ::
        (name .typeAReceiverRouting) ::
          (name .typeALowSurplus) ::
            (name .negativeSupport) ::
              (name .netChargeNegative) ::
                (name .netChargeLocalization) ::
                      (name .netChargeCap) ::
                      (name .netChargeLarge) ::
                      (name .largeBudgetResidual) ::
                        (name .remainderEntropyLow) ::
                          (name .forcedCurvatureCost) ::
                            (name .curvatureFullRank) ::
        (name .curvatureTargetRank) ::
          (name .wedgeSupply) ::
            (name .curvatureDemandFloor) ::
              (name .boundaryDemand) ::
                (name .stubSupply) ::
                  (name .remainderNormalized) ::
                    (name .densityCap) ::
                      (name .barrierCap) ::
                        (name .windowPackageSeparated) ::
                          (name .surplusAtOrBelow) ::
                            (name .localAlgebra) ::
                              (name .maximalPacking) ::
        (name .uncompressible) ::
          (name .tightEndpoint) ::
            (name .slackIndependent) ::
              (name .noProperBaseline) ::
                (name .returnAvoidance) ::
                  [(name .selection)] := rfl

/-- **The node-`[60]` exit records the pressure and not the negative support.**
`cor:global-window-join-pressure` is what the branch on which no negative
admissible support appears carries; `negativeSupport` is absent from its
index. -/
theorem windowJoinPressure_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (residualCWindowJoinPressureKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- The high-entropy large-budget continuation retains node `[52]`'s package
fact and node `[53]`'s complementary verdict. -/
theorem entropyPackage_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected entropyPackageLargeBudgetKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem entropyCapActive_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected entropyCapActiveKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem lowEntropyCapActive_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected lowEntropyCapActiveKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The two exits carry strictly less.**  A branch that left at node `[19]`
never records the near-cubic arm, and a branch that left at node `[21]` never
records the cap -- each exit's audit is its own prefix of the block. -/
theorem surplusAbove_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected surplusAboveKeys) :
    (ExactLedger.audit history).facts =
      [(name .surplusAbove),
        (name .localAlgebra),
        (name .maximalPacking),
        (name .uncompressible),
        (name .tightEndpoint),
        (name .slackIndependent),
        (name .noProperBaseline),
        (name .returnAvoidance),
        (name .selection)] := rfl

theorem barrierOverflow_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected barrierOverflowKeys) :
    (ExactLedger.audit history).facts =
      Core.Residual.closureFactName ::
        [(name .barrierOverflow),
        (name .windowPackageSeparated),
        (name .surplusAtOrBelow),
        (name .localAlgebra),
        (name .maximalPacking),
        (name .uncompressible),
        (name .tightEndpoint),
        (name .slackIndependent),
        (name .noProperBaseline),
        (name .returnAvoidance),
        (name .selection)] := rfl

/-- **The terminal `[37]` closes.**  Its audit is Branch D's index with the
target-defective quotient and, above it, Core's reserved contradiction entry.
No row can spell that name, so the closure is the framework's own statement that
this arm is uninhabited. -/
theorem contextDefect_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected contextDefectKeys) :
    (ExactLedger.audit history).facts =
      Core.Residual.closureFactName ::
        (name .contextDefect) ::
        (name .branchDependence) ::
        (name .curvatureRankDrop) ::
        (name .curvatureTargetRank) ::
        (name .wedgeSupply) ::
        (name .curvatureDemandFloor) ::
        (name .boundaryDemand) ::
        (name .stubSupply) ::
        (name .remainderNormalized) ::
        (name .densityCap) ::
        (name .barrierCap) ::
        (name .windowPackageSeparated) ::
        (name .surplusAtOrBelow) ::
        (name .localAlgebra) ::
        (name .maximalPacking) ::
        (name .uncompressible) ::
        (name .tightEndpoint) ::
        (name .slackIndependent) ::
        (name .noProperBaseline) ::
        (name .returnAvoidance) ::
        [(name .selection)] := rfl

/-- **Every Branch D terminal is accounted for by chronological commits.**

All four are closed round nodes of Part III, and each audit accounts for the
whole branch fact index through `ExactLedger.audit_complete`: nothing was
archived, rebased or dropped on the way to the closure. -/
theorem contextDefect_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected contextDefectKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem atomCompression_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected atomCompressionKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem properDelocalization_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected properDelocalizationKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The rank-drop branch closes.**  Part III's caption is *"Every rank-drop
branch terminates in a closed round node"*, and this is that terminal's audit:
Branch D's certificate, the context-universal determination, the enlarged
support, the whole-graph delocalization, the repair identity, the global
barrier, and Core's reserved contradiction entry on top. -/
theorem rankDropClosed_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected rankDropClosedKeys) :
    (ExactLedger.audit history).facts.take 7 =
      [Core.Residual.closureFactName,
        (name .repairIdentity),
        (name .globalBarrier),
        (name .globalDelocalization),
        (name .delocalizedSupport),
        (name .contextUniversal),
        (name .branchDependence)] := rfl

theorem rankDropClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected rankDropClosedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

end Hypostructure.Graph.Strategy.Spine

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

This module names the spine's row instances at the problem vocabulary.  It does
not provide a second proof history: every executable step is a `Decision.run`,
`factOnly`/`AtomicCT.run`, or framework closure over the incoming `ExactLedger`.
A branch that commits one arm has only that arm's exact key in its type-level
index; all shared predecessor facts remain available because the output index is
literally the new key consed onto the same incoming ledger.
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

/-- Node `[21]`: publish the certified finite enumeration on the unchanged
active residual.  The later independent-window package is not encoded here. -/
@[reducible] noncomputable def finiteBarrierEnumeration :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  barrierEnumerationRow data

/-- Node `[22]`: derive the hot/cold partition from the incoming maximal
packing on the unchanged residual. -/
@[reducible] noncomputable def hotColdPartition :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  hotColdPartitionRow data

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
  localAlgebraRow data

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
    (fun _input fact => by
      rcases fact.down with ⟨packing, packingFacts, card_eq, maximal, cap, stable⟩
      simpa [card_eq] using cap)
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
    (K .uncompressible) (K .remainderNormalized) (K .typeBDisjointLedger)
    (by simp)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down)
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

/-- The paper's Type B bridge sublinearity fact, published as an ordinary
ledger fact after the bridge mass ledger and the shared budget facts are all
present. -/
@[reducible] noncomputable def typeBBridgeSublinear :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeBBridgeSublinearRow

@[reducible] noncomputable def branchKillClosed :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  branchKillClosedRow

@[reducible] noncomputable def largeBudgetRoute8Closed :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  largeBudgetRoute8ClosedRow

noncomputable instance instImpossibleLargeBudgetRoute8Closed :
    Impossible (Input BranchState Presentation presentation data)
      (K .largeBudgetRoute8Closed) where
  contradiction := fun _residual closed => closed.down

/-- Node `[76]`/`[85]`, Step 1 selected fan-entry charge on the B2-success
cursor. -/
@[reducible] noncomputable def typeBSelectedFanCharge :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeBSelectedFanChargeRow (K .fanCertificateMarked) (K .typeBHybridEntry)
    (K .typeBDisjointLedger) (K .typeBSelectedFanCharge) (by simp)
    (fun _input value => ⟨value⟩)

/-- Node `[76]`/`[85]`, the B-ledger charge implication on the B2-success
cursor. -/
@[reducible] noncomputable def typeBExclusionCharge :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeBExclusionChargeRow (K .typeBDisjointLedger)
    (K .typeBSelectedFanCharge) (K .typeBExclusionCharge) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

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
    not_branchDCertificate residual selected.down.1 selected.down.2
      (by
        obtain ⟨packing, valid, quotient, certified, _complete, _inside⟩ :=
          compression.down
        exact ⟨packing, valid, quotient, certified⟩)

noncomputable instance instIncompatibleProperDelocalization :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .properDelocalization) where
  contradiction := fun residual selected smearing =>
    not_branchDCertificate residual selected.down.1 selected.down.2
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
    exact not_globalBarrierReading residual selected.down.1 selected.down.2 reading

noncomputable instance instIncompatibleTypeAExitSixProper :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .typeAExitSixProper) where
  contradiction := fun residual selected proper => by
    obtain ⟨_support, replacement⟩ := proper.down
    exact not_globalBarrierReading residual selected.down.1 selected.down.2
      (Or.inl replacement)

noncomputable instance instIncompatibleTypeAExitSixGlobal :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .typeAExitSixGlobal) where
  contradiction := fun residual selected global => by
    exact not_globalBarrierReading residual selected.down.1 selected.down.2
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

noncomputable instance instImpossibleTypeBExcluded :
    Impossible (Input BranchState Presentation presentation data)
      (K .typeBExcluded) where
  contradiction := fun _residual excluded => excluded.down

/-- **The sparse exit arm closes against the surviving sparse-exit ledger.**

Node `[132]`'s exit arm is the negation of the two clauses node `[125]`
commits: survival of the named sparse exits and absence of proper-support
replacement.  Both are ordinary spine facts, so the branch closes by Core's
`closeIncompatible` whenever both keys are present. -/
noncomputable instance instIncompatibleSparsePairExit :
    Incompatible (Input BranchState Presentation presentation data)
      (K .sparseSurplusSurvivor) (K .sparsePairExit) where
  contradiction := fun _residual survivor exit =>
    survivor.down.1 exit.down

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
    not_contextDefect (data := data) residual value.down

/-- **The near-cubic surplus route closes against node `[19]`.**

The branch enters the sparse-pressure block from `surplusAbove`, so a later
`spineSurplusEstimate` is the exact complementary inequality on the same
selected object.  The contradiction is registered as a framework
incompatibility between ordinary keys; callers close it with `closeIncompatible`
on the incoming ledger and no extra carrier. -/
noncomputable instance instIncompatibleSurplusAboveSpineSurplusEstimate :
    Incompatible (Input BranchState Presentation presentation data)
      (K .surplusAbove) (K .spineSurplusEstimate) where
  contradiction := fun residual above estimate => by
    have lower :
        data.surplusThreshold residual.object.vertexCount <
          residual.object.degreeSurplus data.threshold := by
      change Holds BranchState Presentation presentation data
        .surplusAbove residual.object
      exact above.down
    have upper :
        residual.object.degreeSurplus data.threshold ≤
          data.spineScale * Core.ceilSqrt residual.object.vertexCount := by
      change Holds BranchState Presentation presentation data
        .spineSurplusEstimate residual.object
      exact estimate.down
    exact Nat.not_lt_of_ge (by
      simpa [Data.surplusThreshold] using upper) lower

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

/-- `[76]`/`[85]`: selected fan entries have nonnegative local charge. -/
abbrev fanSelectedFanChargeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBSelectedFanCharge :: fanDisjointLedgerKeys known

/-- `[76]`/`[85]`: the B-ledger exclusion charge implication. -/
abbrev fanExclusionChargeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBExclusionCharge :: fanSelectedFanChargeKeys known

/-- `[76]`/`[85]`, closed arm. -/
abbrev fanExcludedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeBExcluded :: fanExclusionChargeKeys known

/-- `[76]`/`[85]`, surviving residual arm. -/
abbrev fanExclusionResidualKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBExclusionResidual :: fanExclusionChargeKeys known

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

abbrev residualCTypeBExclusionChargeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanExclusionChargeKeys (residualCTypeBCertificateMarkedKeys known)

abbrev residualCTypeBExcludedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanExcludedKeys (residualCTypeBCertificateMarkedKeys known)

abbrev residualCTypeBExclusionResidualKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanExclusionResidualKeys (residualCTypeBCertificateMarkedKeys known)

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

abbrev residualCDegreeFourExclusionChargeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanExclusionChargeKeys (residualCDegreeFourMarkedKeys known)

abbrev residualCDegreeFourExcludedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanExcludedKeys (residualCDegreeFourMarkedKeys known)

abbrev residualCDegreeFourExclusionResidualKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :=
  fanExclusionResidualKeys (residualCDegreeFourMarkedKeys known)

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

/-- Node `[76]`: the B-ledger charge implication after the heavy B2 cursor. -/
abbrev typeBExclusionChargeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBExclusionChargeKeys remainderEntropyLowKeys

/-- Node `[76]`, closed arm. -/
abbrev typeBExcludedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBExcludedKeys remainderEntropyLowKeys

/-- Node `[76]`, surviving residual arm. -/
abbrev typeBExclusionResidualKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCTypeBExclusionResidualKeys remainderEntropyLowKeys

/-- Node `[85]`: exact disjoint post-ledger components, after `[82]`. -/
abbrev degreeFourDisjointLedgerKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourDisjointLedgerKeys remainderEntropyLowKeys

/-- Node `[85]`: the B-ledger charge implication after the degree-four B2 cursor. -/
abbrev degreeFourExclusionChargeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourExclusionChargeKeys remainderEntropyLowKeys

/-- Node `[85]`, closed arm. -/
abbrev degreeFourExcludedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourExcludedKeys remainderEntropyLowKeys

/-- Node `[85]`, surviving residual arm. -/
abbrev degreeFourExclusionResidualKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  residualCDegreeFourExclusionResidualKeys remainderEntropyLowKeys

theorem typeBExcluded_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBExcludedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem typeBExclusionResidual_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBExclusionResidualKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem degreeFourExcluded_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourExcludedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem degreeFourExclusionResidual_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourExclusionResidualKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem typeBExcluded_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBExcludedKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem typeBExclusionResidual_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBExclusionResidualKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem degreeFourExcluded_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourExcludedKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem degreeFourExclusionResidual_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourExclusionResidualKeys) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

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

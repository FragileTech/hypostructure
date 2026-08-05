import Hypostructure.Graph.Strategy.SpineRows

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

/-- The spine's own fact system, installed for the whole run.  It is the only
`FactSystem` on this residual domain, so every key below is one of its own. -/
noncomputable instance instFactSystem :
    FactSystem (Input BranchState Presentation presentation data) :=
  factSystem BranchState Presentation presentation data

/-- The spine's exact semantic keys. -/
abbrev K (k : Key) : FactKey (Input BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.fact k

/-- The residual domain's distinguished closure key, as callers name it.  It is
Core's own reserved key: the vocabulary cannot spell it, which is what makes a
closure entry unforgeable by a row. -/
abbrev closed : FactKey (Input BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.closed

@[simp] theorem closureKey_eq_closed :
    (FactSystem.closureKey :
        FactKey (Input BranchState Presentation presentation data)) = closed :=
  rfl

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

/-- Node `[56]`. -/
@[reducible] noncomputable def netDeficiencyCap :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  netDeficiencyCapRow (K .maximalPacking) (K .stubSupply) (K .densityCap)
    (K .largeOrderResidual) (K .netDeficiencyCap)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _input fact => by
      obtain ⟨_positive, packing, valid, attains, maximal⟩ := fact.down
      exact ⟨packing, valid, attains, maximal⟩)
    (fun _input fact => fact.down)
    (fun _input fact => fact.down)
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
    (K .negativeSupport) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
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
    (K .typeBLocalDichotomy) (by simp)
    (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

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
  degreeFourProfileRow (K .highCentreNormalForm) (K .typeBDegreeFourProfile)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Nodes `[73]`/`[75]` and `[83]`/`[84]`.  One executor value, run after each of
the four bridge-residual cursors: the two fan-certificate residual arms of node
`[71]`/`[80]` and the two overlap-obstruction arms of node `[72]`/`[81]`. -/
@[reducible] noncomputable def bridgeFanMass :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  bridgeFanMassRow (K .highCentreNormalForm) (K .typeBBridgeMass)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Nodes `[76]`/`[85]`, Step 1 of `lem:typeB-exclusion`.  One executor value,
run after either of the two B1 cursors. -/
@[reducible] noncomputable def typeBExclusionCharge :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeBExclusionChargeRow (K .highCentreNormalForm) (K .typeBExclusionCharge)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

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
    obtain ⟨packing, valid, _piece, _inside, _connected, _charge, _positive,
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

/-- **The node-`[60]` terminal is uninhabited**, at the spine's own keys.

Node `[56]` proves that the whole remainder already carries negative net charge,
and node `[59]`'s yes arm says it does not.  That is the manuscript's net-cap
contradiction, `¼|R| ≤ def⁺(R) − σ(R) ≤ τ_win|R| + o(|R|)` with `τ_win < ¼`, and
registering it as `Incompatible` is what lets the framework close the arm the
moment the branch test takes it. -/
noncomputable instance instIncompatibleNetCharge :
    Incompatible (Input BranchState Presentation presentation data)
      (K .netChargeNonNegative) (K .netDeficiencyCap) where
  contradiction := fun _residual nonNegative cap => by
    obtain ⟨packing, valid, maximal, negative⟩ := cap.down
    exact Nat.lt_irrefl _
      (Nat.lt_of_lt_of_le negative (nonNegative.down packing valid maximal))

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
      poolRoom⟩ := package.down packing valid
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
      poolRoom⟩ := package.down packing valid
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

/-- Node `[52]`, reaching the terminal `[54]`: window plus remainder
accounting. -/
abbrev entropyPackageKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .entropyPackageDemand :: remainderEntropyHighKeys

/-- Node `[50]`'s low-entropy arm. -/
abbrev remainderEntropyLowKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .remainderEntropyLow :: forcedCurvatureCostKeys

/-- Node `[53]`'s yes arm, reaching the terminal `[54]`. -/
abbrev entropyCapActiveKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .entropyCapActive :: remainderEntropyLowKeys

/-- Node `[55]`, Residual C: node `[53]`'s no arm. -/
abbrev largeBudgetKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .largeBudgetResidual :: remainderEntropyLowKeys

/-- Node `[55]`, large arm: the manuscript's "for all sufficiently large `n`". -/
abbrev largeOrderKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .largeOrderResidual :: largeBudgetKeys

/-- Node `[55]`, small arm: the finite residue the manuscript's asymptotic
statements do not address. -/
abbrev smallOrderKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .smallOrderResidual :: largeBudgetKeys

/-- Node `[56]`: the large-budget net-deficiency cap. -/
abbrev netDeficiencyCapKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .netDeficiencyCap :: largeOrderKeys

/-- Nodes `[57]`--`[58]`: net charge and its localization. -/
abbrev netChargeLocalizationKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .netChargeLocalization :: netDeficiencyCapKeys

/-- Node `[60]`: the nonnegative arm of node `[59]`, with the window-join
pressure it forces. -/
abbrev windowJoinPressureKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .windowJoinPressure :: K .netChargeNonNegative ::
    netChargeLocalizationKeys

/-- Node `[61]`: the negative arm of node `[59]`, with the connected support it
selects. -/
abbrev negativeSupportKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .negativeSupport :: K .netChargeNegative :: netChargeLocalizationKeys

/-- Node `[63]`, Type A. -/
abbrev typeALowSurplusKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeALowSurplus :: negativeSupportKeys

/-- Node `[88]`: the routing and threshold algebra, on the Type A residual. -/
abbrev typeAReceiverRoutingKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAReceiverRouting :: typeALowSurplusKeys

/-- Node `[89]`, yes arm — the entry of node `[93]`. -/
abbrev typeASaturatedReceiverKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedReceiver :: typeAReceiverRoutingKeys

/-- Node `[89]`, no arm — node `[90]`. -/
abbrev typeAUnsaturatedReceiverKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAUnsaturatedReceivers :: typeAReceiverRoutingKeys

/-- Node `[64]`, Type B. -/
abbrev typeBHighSurplusKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHighSurplus :: negativeSupportKeys

/-- Node `[68]`'s standing law, on the Type B residual. -/
abbrev typeBNormalFormKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .highCentreNormalForm :: typeBHighSurplusKeys

/-- Node `[68]`, yes arm — the entry of node `[69]`. -/
abbrev typeBHeavyCentreKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHeavyCentre :: typeBNormalFormKeys

/-- Node `[69]`: the heavy-centre local dichotomy, on that arm. -/
abbrev typeBLocalDichotomyKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBLocalDichotomy :: typeBHeavyCentreKeys

/-- Node `[70]` on the heavy arm, after `[69]`. -/
abbrev typeBHeavyFanCapKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateCap :: typeBLocalDichotomyKeys


/-- Node `[68]`, no arm — the entry of node `[78]`. -/
abbrev typeBDegreeFourKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDegreeFourCentres :: typeBNormalFormKeys
/-- Node `[70]` on the degree-four arm, after `[78]`'s entry. -/
abbrev typeBDegreeFourFanCapKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateCap :: typeBDegreeFourKeys

/-- Nodes `[78]`--`[79]`: the degree-four fan profile, on that arm. -/
abbrev typeBDegreeFourProfileKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDegreeFourProfile :: typeBDegreeFourFanCapKeys

/-- Node `[80]`, yes arm: the same certificate question at its second position. -/
abbrev degreeFourMarkedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateMarked :: typeBDegreeFourProfileKeys

/-- Node `[80]`, no arm: the fan-mass route `[84]`. -/
abbrev degreeFourResidualKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateResidual :: typeBDegreeFourProfileKeys

/-- Node `[81]`'s first half, closing arm. -/
abbrev degreeFourDirectCycleClosedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeBDirectCycle :: degreeFourMarkedKeys

/-- Node `[81]`'s first half, surviving arm. -/
abbrev degreeFourDirectCycleFreeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDirectCycleFree :: degreeFourMarkedKeys

/-- Node `[81]`, yes arm — the entry of `[82]`. -/
abbrev degreeFourDisjointAssignmentKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDisjointAssignment :: degreeFourDirectCycleFreeKeys

/-- Node `[82]`: the same hybrid ledger row, on the degree-four B2 cursor. -/
abbrev degreeFourHybridEntryKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHybridEntry :: degreeFourDisjointAssignmentKeys

/-- Node `[81]`, no arm — the entry of `[83]`, routed to `[84]`. -/
abbrev degreeFourOverlapObstructionKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBOverlapObstruction :: degreeFourDirectCycleFreeKeys

/-- Node `[71]`, yes arm: every assigned Type B centre is certificate-marked. -/
abbrev typeBCertificateMarkedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateMarked :: typeBHeavyFanCapKeys

/-- Node `[72]`, the closing arm: an assigned centre carries one of the four
direct fan-window configurations, so the branch collides with the selection's own
avoidance and the closure entry is appended. -/
abbrev typeBDirectCycleClosedKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeBDirectCycle :: typeBCertificateMarkedKeys

/-- Node `[72]`, the surviving arm: every closed fan-window pair is
direct-cycle-free, so the local fan-window ledger is complete. -/
abbrev typeBDirectCycleFreeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDirectCycleFree :: typeBCertificateMarkedKeys

/-- Node `[72]`/`[81]`, yes arm — the entry of `[74]`/`[82]`. -/
abbrev typeBDisjointAssignmentKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBDisjointAssignment :: typeBDirectCycleFreeKeys

/-- Node `[74]`: the hybrid B1 fan ledger, on the heavy arm's B2 cursor. -/
abbrev typeBHybridEntryKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBHybridEntry :: typeBDisjointAssignmentKeys

/-- Node `[76]`: Step 1 of `lem:typeB-exclusion`, after `[74]`. -/
abbrev typeBExclusionChargeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBExclusionCharge :: typeBHybridEntryKeys

/-- Node `[85]`: the same row, after `[82]`. -/
abbrev degreeFourExclusionChargeKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBExclusionCharge :: degreeFourHybridEntryKeys

/-- Node `[72]`/`[81]`, no arm — the entry of `[73]`/`[83]`, which the
manuscript routes to the fan-mass node `[75]`/`[84]`. -/
abbrev typeBOverlapObstructionKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBOverlapObstruction :: typeBDirectCycleFreeKeys

/-- Node `[71]`, no arm: a fan-certificate residual centre exists, and the
manuscript routes it to the fan-mass node `[75]`. -/
abbrev typeBCertificateResidualKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .fanCertificateResidual :: typeBHeavyFanCapKeys

/-- Node `[75]`: the fan-mass estimate on the heavy arm's residual cursor. -/
abbrev typeBCertificateResidualMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBBridgeMass :: typeBCertificateResidualKeys

/-- Node `[84]`: the same row, on the degree-four residual cursor. -/
abbrev degreeFourResidualMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBBridgeMass :: degreeFourResidualKeys

/-- Node `[75]` entered from `[73]`: the fan-mass estimate on the heavy arm's
overlap-obstruction cursor. -/
abbrev typeBOverlapObstructionMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBBridgeMass :: typeBOverlapObstructionKeys

/-- Node `[84]` entered from `[83]`: the same row on the degree-four
overlap-obstruction cursor. -/
abbrev degreeFourOverlapObstructionMassKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeBBridgeMass :: degreeFourOverlapObstructionKeys

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
  | entropyPackage
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected entropyPackageKeys)
  | entropyCapActive
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected entropyCapActiveKeys)
  | smallOrderResidual
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected smallOrderKeys)
  | windowJoinPressure
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected windowJoinPressureKeys)
  | typeASaturatedReceiver
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected typeASaturatedReceiverKeys)
  | typeAUnsaturatedReceivers
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected typeAUnsaturatedReceiverKeys)
  | typeBDirectCycleClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected typeBDirectCycleClosedKeys)
  | typeBExclusionCharge
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected typeBExclusionChargeKeys)
  | typeBOverlapObstructionMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected typeBOverlapObstructionMassKeys)
  | typeBCertificateResidualMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected typeBCertificateResidualMassKeys)
  | degreeFourResidualMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected degreeFourResidualMassKeys)
  | degreeFourDirectCycleClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected degreeFourDirectCycleClosedKeys)
  | degreeFourExclusionCharge
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected degreeFourExclusionChargeKeys)
  | degreeFourOverlapObstructionMass
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected degreeFourOverlapObstructionMassKeys)

set_option maxHeartbeats 1200000 in
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
noncomputable def run
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (opened : OpenedScope
      (P := problem BranchState Presentation presentation data) (K .selection)) :
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
                  -- Nodes `[51]`--`[52]`, reaching the terminal `[54]`.
                  exact .entropyPackage
                    ((entropyPackage (data := data)).run highHistory (by simp))
              | .right lowHistory =>
                  -- Node `[53]`: the admissible entropy cap.
                  match entropyCapDichotomy lowHistory (K .entropyCapActive)
                      (K .largeBudgetResidual) (fun active => ⟨active⟩)
                      (fun large => ⟨large⟩) (by simp) (by simp) with
                  | .left activeHistory =>
                      -- Node `[54]`: the entropy cap.  The separated package
                      -- cannot realize more states than there are skeletons, so
                      -- this arm is uninhabited and closes here.
                      exact .entropyCapActive
                        (closeIncompatible activeHistory
                          (K .windowPackageSeparated) (K .entropyCapActive)
                          (by simp))
                  | .right largeHistory =>
                      -- Node `[55]`: the registered order threshold, the
                      -- manuscript's own "for all sufficiently large `n`".
                      match orderThresholdDichotomy largeHistory
                          (K .largeOrderResidual) (K .smallOrderResidual)
                          (fun large => ⟨large⟩) (fun small => ⟨small⟩)
                          (by simp) (by simp) with
                      | .right smallHistory => exact .smallOrderResidual smallHistory
                      | .left orderHistory =>
                      -- Node `[56]`: the net-deficiency cap on Residual C.
                      -- Nodes `[57]`--`[58]`: net charge and its localization.
                      have afterLocalization :=
                        (netChargeLocalization (data := data)).run
                          ((netDeficiencyCap (data := data)).run orderHistory
                            (by simp))
                          (by simp)
                      -- Node `[59]`: the net-charge sign test.
                      match netChargeDichotomy afterLocalization
                          (K .netChargeNonNegative) (K .netChargeNegative)
                          (fun nonNegative => ⟨nonNegative⟩)
                          (fun negative => ⟨negative⟩) (by simp) (by simp) with
                      | .left nonNegativeHistory =>
                          -- Node `[60]`: global window-join pressure, and the
                          -- net-cap contradiction that closes the arm.
                          exact .windowJoinPressure
                            (closeIncompatible
                              ((windowJoinPressure (data := data)).run
                                nonNegativeHistory (by simp))
                              (K .netChargeNonNegative) (K .netDeficiencyCap)
                              (by simp))
                      | .right negativeHistory =>
                          -- Node `[61]`: the connected negative support.
                          have afterSupport :=
                            (negativeSupport (data := data)).run negativeHistory
                              (by simp)
                          -- Node `[62]`: the Type A / Type B split.
                          match typeSplitDichotomy afterSupport
                              (K .negativeSupport) (K .typeALowSurplus)
                              (K .typeBHighSurplus) (fun fact => fact.down)
                              (fun typeA => ⟨typeA⟩) (fun typeB => ⟨typeB⟩)
                              (by simp) (by simp) with
                          | .left typeAHistory =>
                              -- Node `[88]`: the canonical receiver routing of
                              -- the Type A support and its threshold algebra.
                              have afterRouting :=
                                (typeAReceiverRouting (data := data)).run
                                  typeAHistory (by simp)
                              -- Node `[89]`: is some receiver saturated?
                              match typeASaturationDichotomy afterRouting
                                  (K .typeALowSurplus)
                                  (K .typeASaturatedReceiver)
                                  (K .typeAUnsaturatedReceivers)
                                  (fun fact => fact.down)
                                  (fun saturated => ⟨saturated⟩)
                                  (fun unsaturated => ⟨unsaturated⟩)
                                  (by simp) (by simp) with
                              | .left saturatedHistory =>
                                  exact .typeASaturatedReceiver saturatedHistory
                              | .right unsaturatedHistory =>
                                  exact .typeAUnsaturatedReceivers
                                    unsaturatedHistory
                          | .right typeBHistory =>
                              -- Node `[68]`: the high-neighbourhood normal
                              -- form, then the heavy-centre degree split.
                              have afterNormalForm :=
                                (highCentreNormalForm (data := data)).run
                                  typeBHistory (by simp)
                              match heavyCentreDichotomy afterNormalForm
                                  (K .typeBHighSurplus) (K .typeBHeavyCentre)
                                  (K .typeBDegreeFourCentres)
                                  (fun fact => fact.down)
                                  (fun heavy => ⟨heavy⟩)
                                  (fun degreeFour => ⟨degreeFour⟩)
                                  (by simp) (by simp) with
                              | .left heavyHistory =>
                                  -- Node `[69]`: the local dichotomy at a
                                  -- heavy centre.  Node `[70]`: the fan cap.
                                  -- Node `[70]`: the fan cap on this arm.
                                  have afterFanCap :=
                                    (fanCertificateCap (data := data)).run
                                      ((heavyCentreLocalDichotomy
                                        (data := data)).run heavyHistory
                                        (by simp))
                                      (by simp)
                                  -- Node `[71]`: is a certificate labelling
                                  -- present at every assigned centre?
                                  match fanCertificateDichotomy afterFanCap
                                      (K .fanCertificateMarked)
                                      (K .fanCertificateResidual)
                                      (fun marked => ⟨marked⟩)
                                      (fun residual => ⟨residual⟩)
                                      (by simp) (by simp) with
                                  | .left markedHistory =>
                                      -- Node `[72]`, first half: are the direct
                                      -- fan-window and two-window cycles
                                      -- present?  The yes arm collides with the
                                      -- selection's avoidance and closes.
                                      match directCycleDichotomy markedHistory
                                          (K .typeBDirectCycle)
                                          (K .typeBDirectCycleFree)
                                          (fun present => ⟨present⟩)
                                          (fun free => ⟨free⟩)
                                          (by simp) (by simp) with
                                      | .left cycleHistory =>
                                          exact .typeBDirectCycleClosed
                                            (closeIncompatible cycleHistory
                                              (K .selection)
                                              (K .typeBDirectCycle) (by simp))
                                      | .right freeHistory =>
                                          -- Node `[72]`/`[81]`, second half:
                                          -- does the B2 disjoint ledger exist?
                                          match b2AssignmentDichotomy freeHistory
                                              (K .typeBDisjointAssignment)
                                              (K .typeBOverlapObstruction)
                                              (fun ledger => ⟨ledger⟩)
                                              (fun obstruction => ⟨obstruction⟩)
                                              (by simp) (by simp) with
                                          | .left ledgerHistory =>
                                              -- Node `[74]`: the local hybrid B1
                                              -- payment, on the B2 cursor.
                                              -- Node `[76]`: Step 1 of the Type
                                              -- B exclusion, on that cursor.
                                              exact .typeBExclusionCharge
                                                ((typeBExclusionCharge
                                                    (data := data)).run
                                                  ((hybridEntry (data := data)).run
                                                    ledgerHistory (by simp))
                                                  (by simp))
                                          | .right obstructionHistory =>
                                              -- Node `[73]` → `[75]`: the
                                              -- fan-mass estimate on the
                                              -- obstruction cursor.
                                              exact .typeBOverlapObstructionMass
                                                ((bridgeFanMass (data := data)).run
                                                  obstructionHistory (by simp))
                                  | .right residualHistory =>
                                      -- Node `[75]`: the fan-mass estimate on
                                      -- the fan-certificate residual cursor.
                                      exact .typeBCertificateResidualMass
                                        ((bridgeFanMass (data := data)).run
                                          residualHistory (by simp))
                              | .right degreeFourHistory =>
                                  -- Node `[70]` on the degree-four arm: the
                                  -- same executor after the other cursor.
                                  -- Then Part VII: `[79]`, `[80]`, `[81]`.
                                  have afterProfile :=
                                    (degreeFourProfile (data := data)).run
                                      ((fanCertificateCap (data := data)).run
                                        degreeFourHistory (by simp))
                                      (by simp)
                                  -- Node `[80]`: the certificate question at
                                  -- its second position -- the same `Decision`
                                  -- value, after the degree-four cursor.
                                  match fanCertificateDichotomy afterProfile
                                      (K .fanCertificateMarked)
                                      (K .fanCertificateResidual)
                                      (fun marked => ⟨marked⟩)
                                      (fun residual => ⟨residual⟩)
                                      (by simp) (by simp) with
                                  | .right residualHistory =>
                                      -- Node `[84]`: the same fan-mass row on
                                      -- the degree-four residual cursor.
                                      exact .degreeFourResidualMass
                                        ((bridgeFanMass (data := data)).run
                                          residualHistory (by simp))
                                  | .left markedHistory =>
                                      -- Node `[81]`, first half.
                                      match directCycleDichotomy markedHistory
                                          (K .typeBDirectCycle)
                                          (K .typeBDirectCycleFree)
                                          (fun present => ⟨present⟩)
                                          (fun free => ⟨free⟩)
                                          (by simp) (by simp) with
                                      | .left cycleHistory =>
                                          exact .degreeFourDirectCycleClosed
                                            (closeIncompatible cycleHistory
                                              (K .selection)
                                              (K .typeBDirectCycle) (by simp))
                                      | .right freeHistory =>
                                          -- Node `[81]`, second half.
                                          match b2AssignmentDichotomy freeHistory
                                              (K .typeBDisjointAssignment)
                                              (K .typeBOverlapObstruction)
                                              (fun assignment => ⟨assignment⟩)
                                              (fun obstruction => ⟨obstruction⟩)
                                              (by simp) (by simp) with
                                          | .left ledgerHistory =>
                                              -- Node `[82]`: the same executor,
                                              -- after the other B2 cursor, then
                                              -- node `[85]`.
                                              exact .degreeFourExclusionCharge
                                                ((typeBExclusionCharge
                                                    (data := data)).run
                                                  ((hybridEntry (data := data)).run
                                                    ledgerHistory (by simp))
                                                  (by simp))
                                          | .right obstructionHistory =>
                                              -- Node `[83]` → `[84]`.
                                              exact .degreeFourOverlapObstructionMass
                                                ((bridgeFanMass (data := data)).run
                                                  obstructionHistory (by simp))

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
      [`Hypostructure.Graph.Strategy.Spine.curvatureFullRank,
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank,
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply,
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor,
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand,
        `Hypostructure.Graph.Strategy.Spine.stubSupply,
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized,
        `Hypostructure.Graph.Strategy.Spine.densityCap,
        `Hypostructure.Graph.Strategy.Spine.barrierCap,
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated,
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow,
        `Hypostructure.Graph.Strategy.Spine.localAlgebra,
        `Hypostructure.Graph.Strategy.Spine.maximalPacking,
        `Hypostructure.Graph.Strategy.Spine.uncompressible,
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint,
        `Hypostructure.Graph.Strategy.Spine.slackIndependent,
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline,
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance,
        `Hypostructure.Graph.Strategy.Spine.selection] := rfl

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
      `Hypostructure.Graph.Strategy.Spine.typeALowSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

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

/-- **The saturated arm's audit is exactly its facts, in commit order.** -/
theorem typeASaturatedReceiver_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeASaturatedReceiverKeys) :
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
      `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedReceivers ::
        `Hypostructure.Graph.Strategy.Spine.typeAReceiverRouting ::
          `Hypostructure.Graph.Strategy.Spine.typeALowSurplus ::
            `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
              `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
                `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
                  `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
                    `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
                      `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
                        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
                          `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
                            `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
          `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
            `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
              `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
                `Hypostructure.Graph.Strategy.Spine.stubSupply ::
                  `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
                    `Hypostructure.Graph.Strategy.Spine.densityCap ::
                      `Hypostructure.Graph.Strategy.Spine.barrierCap ::
                        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
                          `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
                            `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
                              `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
          `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
            `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
              `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
                `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
                  [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

/-! ### The two arms of node `[68]`

The Type B residual of `[64]` is no longer an exit: node `[68]` commits the
high-neighbourhood normal form on it and then splits on whether some Type B
support carries a centre above the high-centre degree `δ + 1`.  The two indices
below differ in exactly that one entry, and both carry the normal form, which
is what makes it available to `[69]` and to `[78]` alike.

Neither arm can read the other's, and neither can read either arm of node
`[62]`, `[59]`, `[53]`, `[50]`, `[32]`, `[21]` or `[19]` it did not take. -/

/-- **The node-`[72]` closed terminal.**  The closure entry sits on top of the
direct-cycle fact, which sits on the whole certificate-marked history: nothing was
archived to close the arm. -/
theorem typeBDirectCycleClosed_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDirectCycleClosedKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Core.Strategy.contradiction ::
        `Hypostructure.Graph.Strategy.Spine.typeBDirectCycle ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateMarked ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBLocalDichotomy ::
        `Hypostructure.Graph.Strategy.Spine.typeBHeavyCentre ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

/-- **The two arms of node `[72]`/`[81]`.**  Both carry the direct-cycle-free
fact of the first half and the certificate-marked history beneath it, and differ in
exactly one entry: whether B2's disjoint carrier choice exists or the support
carries a minimal overlap obstruction.  Neither can read the other. -/
theorem typeBHybridEntry_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBHybridEntryKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Graph.Strategy.Spine.typeBHybridEntry ::
        `Hypostructure.Graph.Strategy.Spine.typeBDisjointAssignment ::
        `Hypostructure.Graph.Strategy.Spine.typeBDirectCycleFree ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateMarked ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBLocalDichotomy ::
        `Hypostructure.Graph.Strategy.Spine.typeBHeavyCentre ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem typeBOverlapObstruction_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBOverlapObstructionKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Graph.Strategy.Spine.typeBOverlapObstruction ::
        `Hypostructure.Graph.Strategy.Spine.typeBDirectCycleFree ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateMarked ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBLocalDichotomy ::
        `Hypostructure.Graph.Strategy.Spine.typeBHeavyCentre ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem typeBDegreeFourFanCap_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDegreeFourFanCapKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourCentres ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

/-! ### Part VII: the four exits of the degree-four arm

`[79]`'s profile sits on node `[70]`'s cap; `[80]` splits on the certificate
labelling; `[81]` removes the direct cycles and then asks the B2 question.  All
four indices carry `typeBDegreeFourCentres` -- node `[78]`'s own fact -- and none
carries `typeBHeavyCentre`, so no row of this arm can read the heavy arm's
alternative. -/

theorem degreeFourCertificateResidual_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourResidualKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Graph.Strategy.Spine.fanCertificateResidual ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourProfile ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourCentres ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem degreeFourDirectCycleClosed_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourDirectCycleClosedKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Core.Strategy.contradiction ::
        `Hypostructure.Graph.Strategy.Spine.typeBDirectCycle ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateMarked ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourProfile ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourCentres ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem degreeFourHybridEntry_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourHybridEntryKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Graph.Strategy.Spine.typeBHybridEntry ::
        `Hypostructure.Graph.Strategy.Spine.typeBDisjointAssignment ::
        `Hypostructure.Graph.Strategy.Spine.typeBDirectCycleFree ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateMarked ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourProfile ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourCentres ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem degreeFourOverlapObstruction_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourOverlapObstructionKeys) :
    (ExactLedger.audit history).facts =
      `Hypostructure.Graph.Strategy.Spine.typeBOverlapObstruction ::
        `Hypostructure.Graph.Strategy.Spine.typeBDirectCycleFree ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateMarked ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourProfile ::
        `Hypostructure.Graph.Strategy.Spine.fanCertificateCap ::
        `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourCentres ::
        `Hypostructure.Graph.Strategy.Spine.highCentreNormalForm ::
        `Hypostructure.Graph.Strategy.Spine.typeBHighSurplus ::
        `Hypostructure.Graph.Strategy.Spine.negativeSupport ::
        `Hypostructure.Graph.Strategy.Spine.netChargeNegative ::
        `Hypostructure.Graph.Strategy.Spine.netChargeLocalization ::
        `Hypostructure.Graph.Strategy.Spine.netDeficiencyCap ::
        `Hypostructure.Graph.Strategy.Spine.largeOrderResidual ::
        `Hypostructure.Graph.Strategy.Spine.largeBudgetResidual ::
        `Hypostructure.Graph.Strategy.Spine.remainderEntropyLow ::
        `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCost ::
        `Hypostructure.Graph.Strategy.Spine.curvatureFullRank ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem degreeFourCertificateResidual_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourResidualKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem degreeFourDirectCycleClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourDirectCycleClosedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem degreeFourHybridEntry_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourHybridEntryKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem degreeFourOverlapObstruction_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected degreeFourOverlapObstructionKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem typeBDirectCycleClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDirectCycleClosedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem typeBHybridEntry_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBHybridEntryKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem typeBOverlapObstruction_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBOverlapObstructionKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem typeBCertificateResidual_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBCertificateResidualKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem typeBDegreeFourFanCap_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeBDegreeFourFanCapKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The node-`[60]` exit records the pressure and not the negative support.**
`cor:global-window-join-pressure` is what the branch on which no negative
admissible support appears carries; `negativeSupport` is absent from its
index. -/
theorem windowJoinPressure_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected windowJoinPressureKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The two node-`[54]` exits.**  The high-entropy arm reaches the entropy-cap
terminal through node `[52]`'s package accounting; the low-entropy arm reaches
it through node `[53]`'s own comparison.  Neither carries the other's entropy
arm. -/
theorem entropyPackage_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected entropyPackageKeys) :
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

/-- **The two exits carry strictly less.**  A branch that left at node `[19]`
never records the near-cubic arm, and a branch that left at node `[21]` never
records the cap -- each exit's audit is its own prefix of the block. -/
theorem surplusAbove_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected surplusAboveKeys) :
    (ExactLedger.audit history).facts =
      [`Hypostructure.Graph.Strategy.Spine.surplusAbove,
        `Hypostructure.Graph.Strategy.Spine.localAlgebra,
        `Hypostructure.Graph.Strategy.Spine.maximalPacking,
        `Hypostructure.Graph.Strategy.Spine.uncompressible,
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint,
        `Hypostructure.Graph.Strategy.Spine.slackIndependent,
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline,
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance,
        `Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem barrierOverflow_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected barrierOverflowKeys) :
    (ExactLedger.audit history).facts =
      Core.Residual.closureFactName ::
        [`Hypostructure.Graph.Strategy.Spine.barrierOverflow,
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated,
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow,
        `Hypostructure.Graph.Strategy.Spine.localAlgebra,
        `Hypostructure.Graph.Strategy.Spine.maximalPacking,
        `Hypostructure.Graph.Strategy.Spine.uncompressible,
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint,
        `Hypostructure.Graph.Strategy.Spine.slackIndependent,
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline,
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance,
        `Hypostructure.Graph.Strategy.Spine.selection] := rfl

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
        `Hypostructure.Graph.Strategy.Spine.contextDefect ::
        `Hypostructure.Graph.Strategy.Spine.branchDependence ::
        `Hypostructure.Graph.Strategy.Spine.curvatureRankDrop ::
        `Hypostructure.Graph.Strategy.Spine.curvatureTargetRank ::
        `Hypostructure.Graph.Strategy.Spine.wedgeSupply ::
        `Hypostructure.Graph.Strategy.Spine.curvatureDemandFloor ::
        `Hypostructure.Graph.Strategy.Spine.boundaryDemand ::
        `Hypostructure.Graph.Strategy.Spine.stubSupply ::
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized ::
        `Hypostructure.Graph.Strategy.Spine.densityCap ::
        `Hypostructure.Graph.Strategy.Spine.barrierCap ::
        `Hypostructure.Graph.Strategy.Spine.windowPackageSeparated ::
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow ::
        `Hypostructure.Graph.Strategy.Spine.localAlgebra ::
        `Hypostructure.Graph.Strategy.Spine.maximalPacking ::
        `Hypostructure.Graph.Strategy.Spine.uncompressible ::
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint ::
        `Hypostructure.Graph.Strategy.Spine.slackIndependent ::
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline ::
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance ::
        [`Hypostructure.Graph.Strategy.Spine.selection] := rfl

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
        `Hypostructure.Graph.Strategy.Spine.repairIdentity,
        `Hypostructure.Graph.Strategy.Spine.globalBarrier,
        `Hypostructure.Graph.Strategy.Spine.globalDelocalization,
        `Hypostructure.Graph.Strategy.Spine.delocalizedSupport,
        `Hypostructure.Graph.Strategy.Spine.contextUniversal,
        `Hypostructure.Graph.Strategy.Spine.branchDependence] := rfl

theorem rankDropClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected rankDropClosedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

end Hypostructure.Graph.Strategy.Spine

import Hypostructure.Core.Strategy.Dag
import Hypostructure.Core.Strategy.ExactFiniteLocalAlgebraBitTable
import Hypostructure.Graph.Strategy.Official.SealedDag
import Hypostructure.Graph.Strategy.ObstructionPackingClosure
import Hypostructure.Graph.Strategy.HegdeSandeepShashankPacking
import Hypostructure.Graph.Strategy.FiniteDensityBudget
import HypostructureErdos64EG.Problem
import HypostructureErdos64EG.FiniteChecks.P13Barrier.Table

/-!
# Official Erdős problem boundary

The application supplies the mathematical problem, target, and inert
kernel-audited finite presentation data.  It supplies no executor, program
semantics, route, classifier, terminal result, or closure proof.
-/

namespace HypostructureErdos64EG.Official

open Hypostructure
open Hypostructure.Core.Strategy.Official.Features

/-- The literal baseline from the registered EG problem. -/
abbrev Baseline := HypostructureErdos64EG.Baseline

/-- The literal Core problem and target used by the sealed declaration. -/
abbrev problem := HypostructureErdos64EG.problem
abbrev target := HypostructureErdos64EG.target

/-- Residual-owned numeric baseline projected from the already registered
receiver-load presentation.  Graph reconstructs it from the problem
constructor; the application registers no second numeric field. -/
def baselineDegreeQuery :
    Core.Residual.Query (Core.Strategy.ProblemInput problem) fun _ => Nat :=
  Graph.Strategy.minimumDegreeThresholdQuery

/-- The single registered HSS consequence, read through the official cycle
length predicate.  The external order, the external threshold and the exponent
presentation of the axiom's conclusion are all framework-owned. -/
theorem hssHasPowerOfTwoCycle
    (input : Core.Strategy.ProblemInput problem)
    (object : Graph.FiniteObject)
    (minimumDegree : baselineDegreeQuery.read input ≤ object.minDegree)
    (free : Graph.InducedPathFree object
      Graph.External.HegdeSandeepShashank.inducedPathOrder) :
    Graph.HasCycleWithLength PowerOfTwoLength object :=
  Graph.External.HegdeSandeepShashank.hasCycleWithLength
    (fun _length witness =>
      Core.DyadicLength.powerOfTwoLength_of_exists witness)
    (Nat.le_refl _) object minimumDegree free

/-- Single inert induced-path presentation shared by packing and dependent
normalization.  It is the framework's presentation of the registered external
theorem at this problem's registered baseline and target. -/
noncomputable def inducedPathPresentation :
    Graph.Strategy.InducedPathPresentation.{1, 0}
      (Core.Strategy.ProblemInput problem)
      (fun input => target.Predicate input.object) :=
  Graph.Strategy.hegdeSandeepShashankInducedPathPresentation
    erdosReceiverLoadProfile.baselineDegree BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    PowerOfTwoLength
    (fun _length witness =>
      Core.DyadicLength.powerOfTwoLength_of_exists witness)
    (Nat.le_refl _) target (fun _object => Iff.rfl)

private noncomputable def inducedPathPackingSemantics :
    Core.Strategy.ObstructionPackingClosure.Semantics.{1, 1}
      (Core.Strategy.ProblemInput problem)
      (fun input => target.Predicate input.object) :=
  Graph.Strategy.ObstructionPackingClosure.inducedPathSemanticsOfPresentation
    inducedPathPresentation

/-- The finite algebra presentation contains only schedules and the executable
relation already audited by the generated table.  All carrier sizes are
projected from that table's certified profile; the proof DAG supplies no
numerical parameter.

The registration is built through the *denoted* entry point, so the row
indices are not an uninterpreted `Fin 399`: `labelDenotation` names each one by
a legal attachment label of `lem:labels`, bijectively, and identifies the
audited relation with the manuscript's `C_s` on the labels named.  The
generated profile's carrier size is then `lem:labels`' count of those labels by
`LabelDenotation.labels_card`. -/
noncomputable def finiteLocalAlgebra :
    Core.Strategy.ExactFiniteLocalAlgebra.Registration
      (Core.Strategy.ProblemInput problem) :=
  Core.Strategy.ExactFiniteLocalAlgebra.ofDenotedBitRelationTable
    FiniteChecks.P13Barrier.semanticCertificate
    FiniteChecks.P13Barrier.labelDenotation _

/-- The framework-derived definition for the current proof frontier.
Graph installs canonical progress, Core installs the sealed Strategies, and
the problem boundary contributes only residual semantics and audited finite
presentation data. -/
noncomputable def baseDefinition : Core.ProblemDefinition.{1, 0, 0} :=
  let base :=
    Graph.Strategy.Official.SealedDag.minimumDegreeCycleDefinition
    erdosReceiverLoadProfile.baselineDegree
    BranchState
    Graph.ReceiverLoad.LoadCapacityProfile
    erdosReceiverLoadProfile
    PowerOfTwoLength
    target
    (fun _object => Iff.rfl)
    (fun _object => ())
  { base with
    data := {
      base.data with
      coldBranchAggregations := []
      obstructionPackingClosures := [inducedPathPackingSemantics]
      supportComplementNormalizations := []
      boundaryDemandAccountings := []
      localSupplyLowerBounds := []
      -- `finiteStateCapacities` is indexed by the four families above, so a
      -- `with`-update that reassigns any of them must reassign it too;
      -- otherwise the inherited value keeps the stale index and the whole
      -- definition elaborates to `sorry`.
      finiteStateCapacities := []
      route8CarrierClosures := []
      targetRelativeRankDichotomies := []
      compressionLinkedTargetRelativeRankDichotomies := []
      exactFiniteLocalAlgebras := [finiteLocalAlgebra]
      finiteBarrierEnumerations :=
        [Graph.Strategy.FiniteDensityBudget.multiScaleWindowPackage
          (fun input => input.object)
          (FiniteChecks.P13Barrier.enumerationRegistration
            (Core.Strategy.ProblemInput problem))]
    } }

instance baseDefinition_hasObstructionPackingClosure :
    NeZero baseDefinition.data.obstructionPackingClosures.length :=
  ⟨by simp [baseDefinition]⟩

instance baseDefinition_hasExactFiniteLocalAlgebra :
    NeZero baseDefinition.data.exactFiniteLocalAlgebras.length :=
  ⟨by simp [baseDefinition]⟩

instance baseDefinition_hasCounterexampleReduction :
    NeZero baseDefinition.data.counterexampleReductions.length :=
  ⟨by simp [baseDefinition,
    Graph.Strategy.Official.SealedDag.minimumDegreeCycleDefinition,
    Graph.Strategy.Official.SealedDag.minimalCounterexampleDefinition]⟩

instance baseDefinition_hasFiniteBarrierEnumeration :
    NeZero baseDefinition.data.finiteBarrierEnumerations.length :=
  ⟨by simp [baseDefinition]⟩

end HypostructureErdos64EG.Official

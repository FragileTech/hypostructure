import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.PairCode
import Hypostructure.Graph.Contracts.SurplusPair.PairOverlap
import Hypostructure.Graph.Contracts.Spine.PairHandoffSupport
import Hypostructure.Graph.Contracts.Spine.PairHandoffFacts

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[179]`, canonical demand-return input.**

The failed pair is not unpacked by Assembly.  This sealed row reads the exact
node-`[178]` obstruction, recovers its two active demands from membership in
the object's pair schedule, and publishes their already selected canonical
returns and graph-derived `ℓ_ret` bound on the same monotone ledger. -/
@[reducible] noncomputable def pairDemandReturnsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairDemandReturns
    { Requires := [K .pairFailureOverlap]
      Produces := [K .pairDemandReturns]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairDemandReturns)
        ⟨Graph.Contracts.SurplusPair.pairDemandReturns_of_failureOverlap (inputs.get (K .pairFailureOverlap)).down⟩
        .nil)

/-- Node `[179]`: test `lem:pair-system-realizability`'s coverage on G's
canonical return system, read from `K .pairDemandReturns`.  The negative arm is
its literal negation. -/
noncomputable def pairSystemRealizabilityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairDemandReturns) known]
    (coveredFresh : K .pairSystemRealizability ∉ known)
    (failsFresh : K .pairRealizabilityFails ∉ known) :
    Decision (K .pairSystemRealizability) (K .pairRealizabilityFails)
      previous := by
  classical
  exact Decision.run previous (K .pairSystemRealizability)
    (K .pairRealizabilityFails)
    `Hypostructure.Graph.Strategy.Spine.pairSystemRealizabilityDichotomy
    (Classical.choice (show Nonempty
        ((K .pairSystemRealizability).At current ⊕
          (K .pairRealizabilityFails).At current) from by
      obtain ⟨returns, selected⟩ := (previous.get (K .pairDemandReturns)).down
      by_cases covered : Nonempty (PairSystemRealizabilityOutcome returns)
      · exact ⟨.inl ⟨⟨returns, selected, covered⟩⟩⟩
      · exact ⟨.inr ⟨⟨returns, selected, covered⟩⟩⟩))
    coveredFresh failsFresh

/-- Node `[182]` from `[179]`: the failed coverage test retains the literal
canonical demand returns as the uncovered pair-code residual. -/
@[reducible] noncomputable def pairRealizabilityResidualRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairRealizabilityResidual
    { Requires := [K .pairRealizabilityFails, K .pairDemandReturns]
      Produces := [K .pairConditionalFactorizationResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairConditionalFactorizationResidual)
        ⟨Graph.Contracts.SurplusPair.pairUncovered_of_realizabilityFails
          (inputs.get (K .pairDemandReturns)).down
          (inputs.get (K .pairRealizabilityFails)).down⟩
        .nil)

/-- Node `[179]`: does one of alternatives (i)--(iv) of
`lem:pair-system-realizability` occur for G's covered canonical return system
(read from `K .pairSystemRealizability`)?  The paper lists (i)--(iv) before the
serial alternative (v) (tex 5110-5130), so the routed alternatives take
precedence; the split is `Nonempty (PairSystemEarlyOutcome returns)` against
its literal negation at those one pinned returns. -/
noncomputable def pairSystemOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairSystemRealizability) known]
    (earlyFresh : K .pairSystemEarlyOutcome ∉ known)
    (noEarlyFresh : K .pairSystemNoEarlyOutcome ∉ known) :
    Decision (K .pairSystemEarlyOutcome) (K .pairSystemNoEarlyOutcome)
      previous := by
  classical
  exact Decision.run previous (K .pairSystemEarlyOutcome)
    (K .pairSystemNoEarlyOutcome)
    `Hypostructure.Graph.Strategy.Spine.pairSystemOutcomeDichotomy
    (Classical.choice (show Nonempty
        ((K .pairSystemEarlyOutcome).At current ⊕
          (K .pairSystemNoEarlyOutcome).At current) from by
      obtain ⟨returns, returnsSelected, _covered⟩ :=
        (previous.get (K .pairSystemRealizability)).down
      by_cases early : Nonempty (PairSystemEarlyOutcome returns)
      · exact ⟨.inl ⟨⟨returns, returnsSelected, early⟩⟩⟩
      · exact ⟨.inr ⟨⟨returns, returnsSelected, early⟩⟩⟩))
    earlyFresh noEarlyFresh

/-- Node `[179]`, serial arm: with coverage and none of (i)--(iv),
alternative (v) supplies the graph-realized serial demand system. -/
@[reducible] noncomputable def pairSerialDemandSystemRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairSerialDemandSystem
    { Requires := [K .pairSystemRealizability, K .pairSystemNoEarlyOutcome]
      Produces := [K .pairSerialDemandSystem]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairSerialDemandSystem)
        ⟨Graph.Contracts.SurplusPair.pairSerialDemandSystem_of_noEarlyOutcome
          (inputs.get (K .pairSystemRealizability)).down
          (inputs.get (K .pairSystemNoEarlyOutcome)).down⟩
        .nil)

/-- Alternatives (i)--(iv) of node `[179]`: the target cycle and the sparse
exit are excluded by the selection and survivor facts, so alternative (iv), the
first-separator handoff of the retained obstruction at `P₀`, remains and enters
the common Type B entry at its canonical support.  (G audit, `[187]`) The same handoff also
publishes the exact shape and the ambient surplus of that one support
(`K .pairHandoffSupport`, `K .pairHandoffCharge`, `K .pairHandoffNetCharge`). -/
@[reducible] noncomputable def pairSystemEarlyTypeBEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairSystemEarlyTypeBEntry
    { Requires := [K .pairSystemEarlyOutcome, K .selection,
        K .sparseSurplusSurvivor, K .surplusAbove, K .portEndDegree]
      Produces := [K .typeBFanEntry, K .pairHandoffSupport, K .pairHandoffCharge,
        K .pairHandoffNetCharge]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      let handoff :=
        Graph.Contracts.SurplusPair.pairObstructionHandoff_of_pairSystemEarlyOutcome
          (inputs.get (K .pairSystemEarlyOutcome)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .sparseSurplusSurvivor)).down
      .cons (key := K .typeBFanEntry)
        ⟨Graph.Contracts.SurplusPair.typeBFanEntry_of_pairObstructionHandoff
          (inputs.get (K .surplusAbove)).down handoff⟩
        (.cons (key := K .pairHandoffSupport)
          ⟨Graph.Contracts.Spine.PairHandoffSupport.pairHandoffSupport_holds handoff⟩
          (.cons (key := K .pairHandoffCharge)
            ⟨Graph.Contracts.Spine.PairHandoffSupport.pairHandoffCharge_holds
              (inputs.get (K .portEndDegree)).down handoff⟩
            (.cons (key := K .pairHandoffNetCharge)
              ⟨Graph.Contracts.Spine.PairHandoffSupport.pairHandoffNetCharge_holds handoff⟩
              .nil))))

/-- Nodes `[179]` → `[187]` (G audit): the structure of G at the canonical handoff of its pair
obstruction, each fact derived from `K .pairHandoffSupport` and the ledger's own facts. -/
@[reducible] noncomputable def pairHandoffFactsRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairHandoffFacts
    { Requires := [K .pairHandoffSupport, K .selection, K .minDegreeBaseline,
        K .extFreeEmpty, K .newLoadBound, K .highCentreSplitForced,
        K .sameVertexSwitchForcedPath, K .highEndpointSwitch, K .threeRouteFan,
        K .threeRouteChain]
      Produces := [K .pairHandoffHubCharge, K .pairHandoffBoundaryType,
        K .pairHandoffCriticalCoordinate, K .pairObstructionDescent, K .pairHandoffHubForces]
      requiresUnique := by key_fresh
      producesUnique := by key_fresh
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairHandoffHubCharge)
        ⟨Graph.Contracts.Spine.PairHandoffFacts.pairHandoffHubCharge_holds
          (inputs.get (K .pairHandoffSupport)).down (inputs.get (K .extFreeEmpty)).down
          (inputs.get (K .newLoadBound)).down⟩
        (.cons (key := K .pairHandoffBoundaryType)
          ⟨Graph.Contracts.Spine.PairHandoffFacts.pairHandoffBoundaryType_holds
            (inputs.get (K .selection)).down.1 (inputs.get (K .minDegreeBaseline)).down
            (inputs.get (K .pairHandoffSupport)).down⟩
          (.cons (key := K .pairHandoffCriticalCoordinate)
            ⟨Graph.Contracts.Spine.PairHandoffFacts.pairHandoffCriticalCoordinate_holds
              (inputs.get (K .pairHandoffSupport)).down⟩
            (.cons (key := K .pairObstructionDescent)
              ⟨Graph.Contracts.Spine.PairHandoffFacts.pairObstructionDescent_holds
                (inputs.get (K .pairHandoffSupport)).down⟩
              (.cons (key := K .pairHandoffHubForces)
                ⟨Graph.Contracts.Spine.PairHandoffFacts.pairHandoffHubForces_holds
                  (inputs.get (K .pairHandoffSupport)).down
                  (inputs.get (K .highCentreSplitForced)).down
                  (inputs.get (K .sameVertexSwitchForcedPath)).down
                  (inputs.get (K .highEndpointSwitch)).down
                  (inputs.get (K .threeRouteFan)).down (inputs.get (K .threeRouteChain)).down⟩
                .nil)))))

/-- Node `[180]`: test `lem:pair-system-increment-arithmetic`'s coverage on G's
canonical serial system, read from `K .pairSerialDemandSystem`.  The negative
arm is its literal negation. -/
noncomputable def pairIncrementCoveredDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    (coveredFresh : K .pairIncrementCovered ∉ known)
    (failsFresh : K .pairIncrementFails ∉ known) :
    Decision (K .pairIncrementCovered) (K .pairIncrementFails) previous := by
  classical
  exact Decision.run previous (K .pairIncrementCovered)
    (K .pairIncrementFails)
    `Hypostructure.Graph.Strategy.Spine.pairIncrementCoveredDichotomy
    (Classical.choice (show Nonempty
        ((K .pairIncrementCovered).At current ⊕
          (K .pairIncrementFails).At current) from by
      obtain ⟨serial, selected⟩ := (previous.get (K .pairSerialDemandSystem)).down
      by_cases covered : Nonempty (PairIncrementOutcome serial)
      · exact ⟨.inl ⟨⟨serial, selected, covered⟩⟩⟩
      · exact ⟨.inr ⟨⟨serial, selected, covered⟩⟩⟩))
    coveredFresh failsFresh

/-- Node `[182]` from `[180]`: the failed coverage test retains the literal
serial demand system as the uncovered pair-code residual. -/
@[reducible] noncomputable def pairIncrementResidualRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairIncrementResidual
    { Requires := [K .pairIncrementFails, K .pairSerialDemandSystem]
      Produces := [K .pairConditionalFactorizationResidual]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairConditionalFactorizationResidual)
        ⟨Graph.Contracts.SurplusPair.pairUncovered_of_incrementFails
          (inputs.get (K .pairSerialDemandSystem)).down
          (inputs.get (K .pairIncrementFails)).down⟩
        .nil)

/-- Node `[180]`: does a periodic routed alternative of
`lem:pair-system-increment-arithmetic` occur for G's covered canonical serial
system (read from `K .pairIncrementCovered`)?  The node's split (diagram
tex 1213: "periodic sparse-exit/Type B, or full-modulus arithmetic") takes the
periodic outcome first; the split is `Nonempty (PairIncrementEarlyOutcome
serial)` against its literal negation at that one pinned system. -/
noncomputable def pairIncrementOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairIncrementCovered) known]
    (earlyFresh : K .pairIncrementEarlyOutcome ∉ known)
    (noEarlyFresh : K .pairIncrementNoEarlyOutcome ∉ known) :
    Decision (K .pairIncrementEarlyOutcome) (K .pairIncrementNoEarlyOutcome)
      previous := by
  classical
  exact Decision.run previous (K .pairIncrementEarlyOutcome)
    (K .pairIncrementNoEarlyOutcome)
    `Hypostructure.Graph.Strategy.Spine.pairIncrementOutcomeDichotomy
    (Classical.choice (show Nonempty
        ((K .pairIncrementEarlyOutcome).At current ⊕
          (K .pairIncrementNoEarlyOutcome).At current) from by
      obtain ⟨serial, serialSelected, _covered⟩ :=
        (previous.get (K .pairIncrementCovered)).down
      by_cases early : Nonempty (PairIncrementEarlyOutcome serial)
      · exact ⟨.inl ⟨⟨serial, serialSelected, early⟩⟩⟩
      · exact ⟨.inr ⟨⟨serial, serialSelected, early⟩⟩⟩))
    earlyFresh noEarlyFresh

/-- Node `[180]`, arithmetic arm: with coverage and no periodic route, the
corrected full-modulus arithmetic input exists. -/
@[reducible] noncomputable def pairSerialArithmeticRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairSerialArithmetic
    { Requires := [K .pairIncrementCovered, K .pairIncrementNoEarlyOutcome]
      Produces := [K .pairSerialArithmetic]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairSerialArithmetic)
        ⟨Graph.Contracts.SurplusPair.pairSerialArithmetic_of_noEarlyOutcome
          (inputs.get (K .pairIncrementCovered)).down
          (inputs.get (K .pairIncrementNoEarlyOutcome)).down⟩
        .nil)

/-- Node `[180]` (G audit, `[187]`; Lean improvement: `[180]`'s periodic alternatives are empty
after `[179]`'s no-early arm).  The serial system is built on the canonical returns, and each
periodic alternative of `[180]` is the same-named alternative of `[179]`'s early outcome at
those returns (`not_pairIncrementEarly_of_noEarly`).  Hence `K .pairIncrementEarlyOutcome` is
incompatible with `K .pairSystemNoEarlyOutcome`, and the periodic arm of `[180]` closes. -/
noncomputable instance instIncompatiblePairSystemNoEarlyOutcomePairIncrementEarlyOutcome :
    Incompatible (Input BranchState Presentation presentation data)
      (K .pairSystemNoEarlyOutcome) (K .pairIncrementEarlyOutcome) where
  contradiction := fun _current noEarly early =>
    Graph.Contracts.Spine.PairHandoffSupport.not_pairIncrementEarly_of_noEarly
      noEarly.down early.down

end Hypostructure.Graph.Strategy.Spine

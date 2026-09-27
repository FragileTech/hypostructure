import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.PairCode
import Hypostructure.Graph.Contracts.SurplusPair.PairOverlap

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
      · refine ⟨.inr ⟨?_⟩⟩
        rintro ⟨returns', selected', covered'⟩
        obtain rfl := Option.some.inj (selected'.symm.trans selected)
        exact covered covered'))
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

/-- Node `[179]`: is the canonical outcome of G's covered canonical return
system (read from `K .pairSystemRealizability`) one of alternatives (i)--(iv)?
The split is on that one outcome; the negative arm is its literal negation. -/
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
      obtain ⟨returns, returnsSelected, covered⟩ :=
        (previous.get (K .pairSystemRealizability)).down
      obtain ⟨outcome, outcomeSelected⟩ :=
        canonicalRealizabilityOutcome_spec data.toParameters current.object
          returns covered
      cases outcome with
      | early early =>
          exact ⟨.inl ⟨⟨returns, early, returnsSelected, outcomeSelected⟩⟩⟩
      | serial serial same =>
          refine ⟨.inr ⟨?_⟩⟩
          rintro ⟨returns', early', returnsSelected', outcomeSelected'⟩
          obtain rfl := Option.some.inj (returnsSelected'.symm.trans returnsSelected)
          cases outcomeSelected'.symm.trans outcomeSelected))
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
the common Type B entry at its canonical support. -/
@[reducible] noncomputable def pairSystemEarlyTypeBEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairSystemEarlyTypeBEntry
    { Requires := [K .pairSystemEarlyOutcome, K .selection,
        K .sparseSurplusSurvivor, K .surplusAbove]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Graph.Contracts.SurplusPair.typeBFanEntry_of_pairObstructionHandoff
          (inputs.get (K .surplusAbove)).down
          (Graph.Contracts.SurplusPair.pairObstructionHandoff_of_pairSystemEarlyOutcome
            (inputs.get (K .pairSystemEarlyOutcome)).down
            (inputs.get (K .selection)).down.1
            (inputs.get (K .sparseSurplusSurvivor)).down)⟩
        .nil)

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
      · refine ⟨.inr ⟨?_⟩⟩
        rintro ⟨serial', selected', covered'⟩
        obtain rfl := Option.some.inj (selected'.symm.trans selected)
        exact covered covered'))
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

/-- Node `[180]`: is the canonical outcome of G's covered canonical serial
system (read from `K .pairIncrementCovered`) a periodic routed alternative?
The split is on that one outcome; the negative arm is its literal negation. -/
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
      obtain ⟨serial, serialSelected, covered⟩ :=
        (previous.get (K .pairIncrementCovered)).down
      obtain ⟨outcome, outcomeSelected⟩ :=
        canonicalIncrementOutcome_spec data.toParameters current.object
          serial covered
      cases outcome with
      | early early =>
          exact ⟨.inl ⟨⟨serial, early, serialSelected, outcomeSelected⟩⟩⟩
      | arithmetic arithmetic =>
          refine ⟨.inr ⟨?_⟩⟩
          rintro ⟨serial', early', serialSelected', outcomeSelected'⟩
          obtain rfl := Option.some.inj (serialSelected'.symm.trans serialSelected)
          cases outcomeSelected'.symm.trans outcomeSelected))
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

/-- The periodic alternatives of node `[180]`: the sparse exit is excluded by
the survivor fact, so the first-separator handoff of the serial system's own
obstruction remains and enters the common Type B entry at its canonical
support. -/
@[reducible] noncomputable def pairIncrementEarlyTypeBEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairIncrementEarlyTypeBEntry
    { Requires := [K .pairIncrementEarlyOutcome, K .sparseSurplusSurvivor,
        K .surplusAbove]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        ⟨Graph.Contracts.SurplusPair.typeBFanEntry_of_pairObstructionHandoff
          (inputs.get (K .surplusAbove)).down
          (Graph.Contracts.SurplusPair.pairObstructionHandoff_of_pairIncrementEarlyOutcome
            (inputs.get (K .pairIncrementEarlyOutcome)).down
            (inputs.get (K .sparseSurplusSurvivor)).down)⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine

import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

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
        (show Value BranchState Presentation presentation data
            .pairDemandReturns inputs.current from
          ⟨⟨PairDemandReturns.of
            (Classical.choice
              (inputs.get (K .pairFailureOverlap)).down)⟩⟩)
        .nil)

/-- Node `[179]` / open node `[182]`: test the five alternatives of
`lem:pair-system-realizability` on the one exact overlap obstruction already
stored in the ledger. -/
noncomputable def pairSystemRealizabilityDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairDemandReturns) known]
    (coveredFresh : K .pairSystemRealizability ∉ known)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known) :
    Decision (K .pairSystemRealizability)
      (K .pairConditionalFactorizationResidual) previous := by
  classical
  let returns := Classical.choice
    (previous.get (K .pairDemandReturns)).down
  exact Decision.run previous (K .pairSystemRealizability)
    (K .pairConditionalFactorizationResidual)
    `Hypostructure.Graph.Strategy.Spine.pairSystemRealizabilityDichotomy
    (if covered : Nonempty (PairSystemRealizabilityOutcome returns) then
      .inl ⟨⟨returns, covered⟩⟩
    else
      .inr ⟨⟨.systemRealizability returns covered⟩⟩)
    coveredFresh residualFresh

/-- Node `[179]`: split the already-published five-way theorem into its
closed/routed alternatives (i)--(iv) and its serial alternative (v). -/
noncomputable def pairSystemOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairSystemRealizability) known]
    (earlyFresh : K .pairSystemEarlyOutcome ∉ known)
    (serialFresh : K .pairSerialDemandSystem ∉ known) :
    Decision (K .pairSystemEarlyOutcome) (K .pairSerialDemandSystem)
      previous := by
  classical
  let package := Classical.choice
    (previous.get (K .pairSystemRealizability)).down
  let outcome := Classical.choice package.2
  exact Decision.run previous (K .pairSystemEarlyOutcome)
    (K .pairSerialDemandSystem)
    `Hypostructure.Graph.Strategy.Spine.pairSystemOutcomeDichotomy
    (match outcome with
    | .early early => .inl ⟨⟨early⟩⟩
    | .serial serial _same => .inr ⟨⟨serial⟩⟩)
    earlyFresh serialFresh

/-- Alternatives (i)--(iv) of node `[179]` are either already contradictory
to the selected/survivor facts or are the literal common Type B entry.  This
row publishes that entry only after reading all three facts from ExactLedger. -/
@[reducible] noncomputable def pairSystemEarlyTypeBEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairSystemEarlyTypeBEntry
    { Requires := [K .pairSystemEarlyOutcome, K .selection,
        K .sparseSurplusSurvivor]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        (show Value BranchState Presentation presentation data
            .typeBFanEntry inputs.current from ⟨by
          let outcome := Classical.choice
            (inputs.get (K .pairSystemEarlyOutcome)).down
          match outcome with
          | .targetCycle cycle =>
              exact False.elim ((inputs.get (K .selection)).down.1 cycle)
          | .sparseExit exit =>
              exact False.elim
                ((inputs.get (K .sparseSurplusSurvivor)).down exit)
          | .typeB entry => exact entry⟩)
        .nil)

/-- Node `[180]` / open node `[182]`: test the exact serial system against the
corrected full-modulus arithmetic and the two periodic-response routes claimed
by `lem:pair-system-increment-arithmetic`. -/
noncomputable def pairIncrementCoveredDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairSerialDemandSystem) known]
    (coveredFresh : K .pairIncrementCovered ∉ known)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known) :
    Decision (K .pairIncrementCovered)
      (K .pairConditionalFactorizationResidual) previous := by
  classical
  let serial := Classical.choice
    (previous.get (K .pairSerialDemandSystem)).down
  exact Decision.run previous (K .pairIncrementCovered)
    (K .pairConditionalFactorizationResidual)
    `Hypostructure.Graph.Strategy.Spine.pairIncrementCoveredDichotomy
    (if covered : Nonempty (PairIncrementOutcome serial) then
      .inl ⟨⟨serial, covered⟩⟩
    else
      .inr ⟨⟨.incrementArithmetic serial covered⟩⟩)
    coveredFresh residualFresh

/-- Node `[180]`: split its published exhaustive alternative into the periodic
route and the corrected direct arithmetic input. -/
noncomputable def pairIncrementOutcomeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairIncrementCovered) known]
    (earlyFresh : K .pairIncrementEarlyOutcome ∉ known)
    (arithmeticFresh : K .pairSerialArithmetic ∉ known) :
    Decision (K .pairIncrementEarlyOutcome) (K .pairSerialArithmetic)
      previous := by
  classical
  let package := Classical.choice
    (previous.get (K .pairIncrementCovered)).down
  let outcome := Classical.choice package.2
  exact Decision.run previous (K .pairIncrementEarlyOutcome)
    (K .pairSerialArithmetic)
    `Hypostructure.Graph.Strategy.Spine.pairIncrementOutcomeDichotomy
    (match outcome with
    | .early early => .inl ⟨⟨early⟩⟩
    | .arithmetic arithmetic => .inr ⟨⟨package.1, ⟨arithmetic⟩⟩⟩)
    earlyFresh arithmeticFresh

/-- The periodic sparse-exit/Type-B alternative of node `[180]`, normalized
to the common Type B entry after eliminating the survivor-incompatible exit. -/
@[reducible] noncomputable def pairIncrementEarlyTypeBEntryRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairIncrementEarlyTypeBEntry
    { Requires := [K .pairIncrementEarlyOutcome, K .sparseSurplusSurvivor]
      Produces := [K .typeBFanEntry]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .typeBFanEntry)
        (show Value BranchState Presentation presentation data
            .typeBFanEntry inputs.current from ⟨by
          let outcome := Classical.choice
            (inputs.get (K .pairIncrementEarlyOutcome)).down
          match outcome with
          | .sparseExit exit =>
              exact False.elim
                ((inputs.get (K .sparseSurplusSurvivor)).down exit)
          | .typeB entry => exact entry⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine

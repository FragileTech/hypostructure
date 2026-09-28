import HypostructureErdos64EG.Assembly.Residuals
import HypostructureErdos64EG.Assembly.Residuals.Route8Blocks

/-!
# Assembly: Residuals / ArmBlocks

The arm evidence threaded through the shared functions of the near-cubic
survivor, so that every return site states the residual of its own path.

A shared function reached from several upstream arms takes ONE explicit
argument: a proof of a `Prop` about `G` naming the arm the path took.  The
proof is a disjunction or conjunction of arm blocks (`Route8Blocks.lean` and
the blocks below), each built at the call site where the arm's keys are in
scope, by the block's `.ret` with one `get` per key from the single
`ExactLedger`.  All keys persist on that one ledger, so carrying the block's
proof down to the return site is still one `get` per key on it.  The argument
is never a ledger or a history.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

-- The `[160]` arm on which the dense hot/cold pass `[162]` runs.
/-- Dense-pass arm: `[160]` first test fails, `τ(θ) ≥ 1/4` (1 fact). -/
abbrev DenseTauBlock_atOrAbove (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object

/-- `DenseTauBlock_atOrAbove` from the one ledger: one `get` per key. -/
theorem DenseTauBlock_atOrAbove.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known] :
    DenseTauBlock_atOrAbove selected :=
  (history.get (K .denseDeficiencyAtOrAbove)).down

/-- Dense-pass arm: `[160]` first test holds, `τ(θ) < 1/4`, and the
private-carrier rate `τ(θ) < 3/13` fails (2 facts). -/
abbrev DenseTauBlock_belowRateFails (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object

/-- `DenseTauBlock_belowRateFails` from the one ledger: one `get` per key. -/
theorem DenseTauBlock_belowRateFails.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .route8RateFails) known] :
    DenseTauBlock_belowRateFails selected :=
  ⟨(history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .route8RateFails)).down⟩

/-- The `[160]` arm of the dense pass `[162]` (`nearCubicDenseLinear`,
`selectedCanonicalReplacementContinuation`). -/
abbrev DenseTauArm (selected : EGInput.{u}) : Prop :=
  DenseTauBlock_atOrAbove selected ∨ DenseTauBlock_belowRateFails selected

-- The arms into the four spine exits `nearCubicLargeBudget*`.
/-- The two routes into `nearCubicLargeBudgetColdRate` (the `[147]` arm):
realized package, or unrealized package with `τ(θ) ≥ 1/4`. -/
abbrev ColdRateArm (selected : EGInput.{u}) : Prop :=
  Route8LanePrefixBlock_realizedColdBelow selected ∨
  Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow selected

theorem ColdRateArm.toPrefix {selected : EGInput.{u}}
    (arm : ColdRateArm selected) : Route8LanePrefix selected := by
  rcases arm with p | p
  · exact Or.inl p
  · exact Or.inr (Or.inr (Or.inl p))

/-- The two routes into `nearCubicLargeBudgetDensityCap` (the `[24]` arm):
realized package, or unrealized package with `τ(θ) ≥ 1/4`. -/
abbrev DensityCapArm (selected : EGInput.{u}) : Prop :=
  Route8LanePrefixBlock_realizedColdAtOrAbove selected ∨
  Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected

theorem DensityCapArm.toPrefix {selected : EGInput.{u}}
    (arm : DensityCapArm selected) : Route8LanePrefix selected := by
  rcases arm with p | p
  · exact Or.inr (Or.inl p)
  · exact Or.inr (Or.inr (Or.inr (Or.inl p)))

-- The arms carried along the net-charge continuation.
/-- The arms fixed on entry to the net-charge continuation `[57]`: the
near-cubic prefix and the entropy arm of `[50]`--`[55]`. -/
abbrev NetChargeArms (selected : EGInput.{u}) : Prop :=
  Route8LanePrefix selected ∧ EntropyArm selected

/-- The arms at the unified route-`8` return: prefix, entropy and the whole
net-charge continuation. -/
abbrev Route8Arms (selected : EGInput.{u}) : Prop :=
  Route8LanePrefix selected ∧ EntropyArm selected ∧ NetChargeContinuation selected

/-- Type A lane after `[86]`'s visible-entry split. -/
abbrev TypeAEntryArms (selected : EGInput.{u}) : Prop :=
  NetChargeArms selected ∧ TypeAEntry selected

/-- Type A lane after the exit-`(4)` descent is published. -/
abbrev TypeALaneArms (selected : EGInput.{u}) : Prop :=
  TypeAEntryArms selected ∧ NetChargeLaneBlock_typeALowSurplus selected

/-- Type A lane after the exit-`(4)` split. -/
abbrev TypeAExitFourArms (selected : EGInput.{u}) : Prop :=
  TypeALaneArms selected ∧ TypeAExitFour selected

/-- The lane arms fixed before the common Type B chain `[67]`--`[85]`: the
Type A decorated handoff or the Type B high-surplus lane (the absorbed lane
`[177]` is not entered: `[173]`'s no-arm is closed against `K .route8Rate`). -/
abbrev BChainLane (selected : EGInput.{u}) : Prop :=
  (NetChargeLaneBlock_typeALowSurplus selected ∧ TypeAEntry selected ∧
      TypeAArmBlock_decorated selected ∧ TypeAExitFour selected) ∨
    NetChargeLaneBlock_typeBHighSurplus selected

/-- The arms on entry to the common Type B chain. -/
abbrev BChainArms (selected : EGInput.{u}) : Prop :=
  NetChargeArms selected ∧ BChainLane selected

/-- The fan block of the fan arm the Type B chain took, named by the
certificate walk's `degreeFour` argument (`none`: heavy centre, `some`: the
degree-four centres of `[78]`). -/
def BChainFanFor (selected : EGInput.{u}) {known : FactKeys EGInput.{u}} :
    Option (FactKeys.Has (K .typeBFanDegreeFourCentres) known) → Prop
  | none => BChainFanBlock_heavyCentre selected
  | some _ => BChainFanBlock_degreeFour selected

/-- The certificate residual arm `[75]`/`[84]` after either fan arm. -/
theorem BChainFanFor.residual {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    {degreeFour : Option (FactKeys.Has (K .typeBFanDegreeFourCentres) known)}
    (fan : BChainFanFor selected degreeFour)
    (residual : BChainCertificateBlock_residual selected) :
    BChainFanCertificate selected := by
  cases degreeFour with
  | none => exact Or.inl ⟨fan, Or.inl residual⟩
  | some _ => exact Or.inr ⟨fan, Or.inl residual⟩

/-- A B-chain lane together with the B-chain it ran is one net-charge
continuation arm. -/
theorem BChainLane.continuation {selected : EGInput.{u}}
    (lane : BChainLane selected) (chain : BChain selected) :
    NetChargeContinuation selected := by
  rcases lane with ⟨low, entry, decorated, exitFour⟩ | high
  · exact Or.inl ⟨low, entry, Or.inl ⟨decorated, exitFour, chain⟩⟩
  · exact Or.inr ⟨high, chain⟩

/-- The route-`8` arms once the B-chain is complete. -/
theorem BChainArms.route8 {selected : EGInput.{u}}
    (arms : BChainArms selected) (chain : BChain selected) :
    Route8Arms selected :=
  ⟨arms.1.1, arms.1.2, arms.2.continuation chain⟩

/-- The Type A route-`8` residual arm (`[109]` → `[113]`): the lane arms, the
arm's own block and the `[113]` deficit-fails block give the route-`8` arms
(the deficit-holds arm closes at `[124]`). -/
theorem TypeAExitFourArms.route8Residual {selected : EGInput.{u}}
    (arms : TypeAExitFourArms selected)
    (residual : TypeAArmBlock_route8Residual selected)
    (deficit : Route8DeficitBlock_fails selected) : Route8Arms selected :=
  ⟨arms.1.1.1.1, arms.1.1.1.2,
    Or.inl ⟨arms.1.2, arms.1.1.2, Or.inr (Or.inl ⟨residual, arms.2, deficit⟩)⟩⟩

/-- The Type A decorated-handoff arm (`[108]`): the lane arms and the arm's own
block are the B-chain arms. -/
theorem TypeAExitFourArms.decorated {selected : EGInput.{u}}
    (arms : TypeAExitFourArms selected)
    (decorated : TypeAArmBlock_decorated selected) : BChainArms selected :=
  ⟨arms.1.1.1, Or.inl ⟨arms.1.2, arms.1.1.2, decorated, arms.2⟩⟩

/-- The Type A exit-`(4)` discharged retest arm: the lane arms and the arm's
own block give the route-`8` arms. -/
theorem TypeALaneArms.dischargedRetest {selected : EGInput.{u}}
    (arms : TypeALaneArms selected)
    (retest : TypeAArmBlock_dischargedRetest selected) : Route8Arms selected :=
  ⟨arms.1.1.1, arms.1.1.2, Or.inl ⟨arms.2, arms.1.2, Or.inr (Or.inr retest)⟩⟩

/-- The Type B high-surplus lane (`[64]`): the net-charge arms and the lane
block are the B-chain arms. -/
theorem NetChargeArms.typeBHighSurplus {selected : EGInput.{u}}
    (arms : NetChargeArms selected)
    (lane : NetChargeLaneBlock_typeBHighSurplus selected) : BChainArms selected :=
  ⟨arms, Or.inr lane⟩

end HypostructureErdos64EG

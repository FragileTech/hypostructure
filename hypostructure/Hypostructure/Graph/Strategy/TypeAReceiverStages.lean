import Hypostructure.Graph.TypeAReceiverClosure

/-!
# The Type A stage chain, manuscript nodes `[86]`--`[92]`

Figure 8's Type A spine, written the way every other stage chain in this
framework is written: one `Core.Residual.Ledger.Extension` per manuscript fact,
each retaining its complete predecessor literally and adding exactly one value.
`Core.Strategy.FiniteStateNetChargeContinuation`'s `Stage56`--`Stage62` is the
template, and this chain continues it from the node-`[63]` Type A residual.

Nothing is transported by hand.  Each stage reads the facts it needs off the
inherited ledger through the queries the producing Strategy published, and the
framework's own `preserve` / `preserveProp` carry the capacity and density
ledgers forward.
-/

namespace Hypostructure.Graph.Strategy.TypeAReceiverStages

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.FiniteStateNetChargeContinuation

universe uPrevious uResidual

variable {Previous : Type uPrevious} {Residual : Type uResidual}
variable [HasResidual Previous Residual]
variable (profile : Profile Previous Residual)
variable {stubRate windowCount : Nat}

/-! ## Manuscript node `[86]`: the Type A support

`def:typeA-support`: *"A Type A support is a connected admissible support `X`
with `σ(X) = 0` … In the negative-net-charge branch a Type A support also
satisfies `def⁺(X) < |V(X)|/4`."*

Both halves are already on the inherited ledger.  `σ(X) = 0` is the node-`[63]`
residual's own `TypeAResidual.noSurplus`.  The quarter bound is the left
alternative of `LocalSupplyLowerBound.Summary.negativeNetCharge_or_windowStubExcess`,
read at the node-`[62]` capacity ledger; its three premises are CT9's own
partition facts, and its right alternative is the window-stub excess that
`cor:global-window-join-pressure` routes to nodes `[135]`--`[136]`, which is not
this branch.

This stage therefore adds one value: the manuscript's `def⁺(X) < |V(X)|/4`. -/

/-- The local-supply ledger entry the node-`[63]` residual carries. -/
abbrev summaryAt {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Core.Strategy.LocalSupplyLowerBound.Summary :=
  profile.capacity62.localSupply.read residual.stage

/-- **Manuscript node `[86]`.**  `def⁺(X) - σ(X) < |V(X)|/4`, with the quarter
cleared, in the published ledger coordinates.  This is `def:net-charge`'s
`No(X) < 0` for the support node `[61]` selected. -/
abbrev NegativeCharge86 {previous : Previous}
    (residual : profile.TypeAResidual previous) : Prop :=
  4 * (((summaryAt profile residual).requiredMass : Int) -
        ((summaryAt profile residual).assignedSurplus : Int)) <
    ((summaryAt profile residual).netDeficiency.remainder : Int)

/-- The window-stub excess: the right alternative of the ledger's own
disjunction.  `cor:global-window-join-pressure` reads it as `σ_W > σ_R` and
routes it to nodes `[135]`--`[136]`; it is not a Type A alternative. -/
abbrev WindowStubExcess86 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (stubRate windowCount : Nat) : Prop :=
  ((stubRate * windowCount : Nat) : Int) <
    ((summaryAt profile residual).requiredMass : Int) -
      ((summaryAt profile residual).assignedSurplus : Int)

/-- **The complete node-`[86]` alternative.**  Both arms of the ledger's own
published disjunction, retained.  The left arm is the Type A negative charge;
the right arm is the window-stub excess, which `cor:global-window-join-pressure`
turns into `σ_W > σ_R` and the manuscript routes to nodes `[135]`--`[136]`.
Neither is discarded here: the stage records the disjunction and a later
decision selects. -/
abbrev NetChargeAlternative86 {previous : Previous}
    (residual : profile.TypeAResidual previous) : Prop :=
  ∀ windowOrder stubRate windowCount : Nat,
    (summaryAt profile residual).selectedCount = windowOrder * windowCount →
      (summaryAt profile residual).netDeficiency.remainder +
          (summaryAt profile residual).selectedCount =
            (summaryAt profile residual).ambientCount →
        (4 * stubRate + windowOrder) * windowCount <
            (summaryAt profile residual).ambientCount →
          NegativeCharge86 profile residual ∨
            WindowStubExcess86 profile residual stubRate windowCount

/-- Manuscript node `[86]` as a ledger stage: the complete node-`[62]` stage,
retained literally, extended by the node-`[86]` alternative. -/
abbrev Stage86 {previous : Previous}
    (residual : profile.TypeAResidual previous) :=
  Ledger.Extension profile.Stage62
    (fun _ => NetChargeAlternative86 profile residual)

/-- Build the node-`[86]` stage by reading the inherited ledger.

Nothing is handed in.  The CT9 selected/complement facts and
`prop:p13-density`'s cap are premises *of the published implication*, exactly as
in `DensityCap56`, `RateCap56` and `NetCapContradiction60`, so a consumer
instantiates them at its own packing rather than the builder consuming them.
The value appended is the ledger's own disjunction, verbatim. -/
noncomputable def stage86 {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Stage86 profile residual :=
  Ledger.extend residual.stage
    (fun _windowOrder _stubRate _windowCount windowCover partition densityCap =>
      (summaryAt profile residual).negativeNetCharge_or_windowStubExcess
        windowCover partition densityCap)

/-- The node-`[86]` stage retains the node-`[62]` stage literally. -/
@[simp] theorem stage86_previous {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    (stage86 profile residual).previous = residual.stage := rfl

/-- Recover the node-`[86]` alternative from the stage, through the ledger
API.  Both arms come back; the consumer selects. -/
def alternative86Query {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Query (Stage86 profile residual)
      (fun _ => NetChargeAlternative86 profile residual) :=
  Query.latest

/-- The node-`[62]` capacity ledger, carried onto the node-`[86]` stage by the
framework's own preservation. -/
def capacity86 {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    CapacityLedger (Stage86 profile residual) :=
  profile.capacity62.preserveProp
    (Added := fun _ =>
      NetChargeAlternative86 profile residual)

/-- The node-`[62]` density ledger, likewise. -/
def density86 {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Core.Strategy.FiniteDensityBudget.CapLedger
      (Stage86 profile residual) :=
  profile.density62.preserveProp
    (Added := fun _ =>
      NetChargeAlternative86 profile residual)

/-! ## Manuscript node `[89]`: the saturated-receiver decision

The manuscript asks whether some receiver carries `L(w) ≥ 4q(w)`.  Aggregated
over the support that is exactly the comparison `lem:typeA-unsaturated-discharge`
turns into: if every receiver is unsaturated the discharge gives
`|V(X)| ≤ 4 · def⁺(X)`, and if some receiver is saturated it does not.

So the split is a `Core.Residual.Decision.Binary` on the two published ledger
numbers, built exactly as `Decision62` is, by
`Core.OrderThresholdSplit.DependentProfileFamily.strictDecisionNode`.  Both arms
are recorded on the ledger; nothing is chosen away. -/

private def comparison89 {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Core.OrderThresholdSplit.Profile Nat :=
  { value := (summaryAt profile residual).netDeficiency.remainder
    threshold := 4 * (summaryAt profile residual).requiredMass }

/-- The saturated arm: the remainder exceeds the discharge capacity, so some
receiver carries `L(w) ≥ 4q(w)` and the exit chain at `[93]` applies. -/
abbrev Saturated89 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (_stage : Stage86 profile residual) : Prop :=
  (comparison89 profile residual).threshold <
    (comparison89 profile residual).value

/-- The unsaturated arm.  Its payload *is* the node-`[91]` discharge: every
receiver satisfies `L(w) ≤ 4q(w) - 1`, so `lem:typeA-unsaturated-discharge`
gives `|V(X)| ≤ 4 · def⁺(X)` in the published coordinates. -/
abbrev Unsaturated89 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (_stage : Stage86 profile residual) : Prop :=
  (comparison89 profile residual).value ≤
    (comparison89 profile residual).threshold

abbrev Decision89 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (stage : Stage86 profile residual) :=
  Core.Residual.Decision.Binary
    (Saturated89 profile residual) (Unsaturated89 profile residual) stage

/-- Manuscript node `[89]` as a ledger stage. -/
abbrev Stage89 {previous : Previous}
    (residual : profile.TypeAResidual previous) :=
  Ledger.Extension (Stage86 profile residual)
    (Decision89 profile residual)

private noncomputable def comparison89Family {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Core.OrderThresholdSplit.DependentProfileFamily Unit
      (fun _ => Stage86 profile residual) Nat :=
  { profile := fun _ _ => comparison89 profile residual }

/-- Append the node-`[89]` decision by running the framework's own strict
decision node on the two published numbers. -/
noncomputable def stage89 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (stage : Stage86 profile residual) :
    Stage89 profile residual :=
  ((comparison89Family profile residual).strictDecisionNode
    (residual := ())).run stage

/-- Recover the node-`[89]` decision from the stage. -/
def decision89Query {previous : Previous}
    (residual : profile.TypeAResidual previous) :
    Query (Stage89 profile residual)
      (fun stage => Decision89 profile residual stage.previous) :=
  Query.latest

/-! ## Manuscript nodes `[91]`--`[92]`: the discharge and its contradiction

`lem:typeA-unsaturated-discharge` gives `|V(X)| ≤ loadMultiplier · def⁺(X)` on
the node-`[89]` no-branch.  Read in the published coordinates that is
`remainder ≤ 4 · requiredMass`, and it contradicts the node-`[86]` fact this
ledger already carries.  That contradiction is manuscript node `[92]`,
"unsaturated Type A charge closes". -/

/-- **Manuscript node `[91]`.**  The `3/7/11` charge bound in ledger
coordinates. -/
abbrev Discharge91 {previous : Previous}
    (residual : profile.TypeAResidual previous) : Prop :=
  (summaryAt profile residual).netDeficiency.remainder ≤
    4 * (summaryAt profile residual).requiredMass

/-- Manuscript node `[91]` as a ledger stage on top of the node-`[89]`
decision.  Its added value is the discharge, which is definitionally the
`Unsaturated89` arm the decision already recorded. -/
abbrev Stage91 {previous : Previous}
    (residual : profile.TypeAResidual previous) :=
  Ledger.Extension (Stage89 profile residual)
    (fun _ => Discharge91 profile residual)

/-- Append the discharge to the ledger by **reading the node-`[89]` decision**.

Nothing is handed in: `Unsaturated89` is definitionally
`remainder ≤ 4 · requiredMass`, which is `Discharge91`, so the no-branch payload
the decision already recorded *is* the node-`[91]` fact.  The caller selects the
arm; it does not supply the conclusion. -/
noncomputable def stage91 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (stage : Stage89 profile residual)
    (unsaturated : Unsaturated89 profile residual stage.previous) :
    Stage91 profile residual :=
  Ledger.extend stage unsaturated

/-- **Manuscript node `[92]`: the unsaturated Type A charge closes.**

The node-`[86]` fact and the node-`[91]` discharge are both on this ledger and
are exact opposites once `σ(X) = 0` is read off the residual, so the branch is
impossible.  Nothing is recomputed: `negative` is retrieved from the `[86]`
stage, `discharge` from the `[91]` stage, and `noSurplus` is the node-`[63]`
residual's own field. -/
theorem contradiction92 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (negative : NegativeCharge86 profile residual)
    (discharge : Discharge91 profile residual) : False := by
  exact (summaryAt profile residual).unsaturatedChargeContradiction
    residual.noSurplus negative discharge

/-- The node-`[92]` closure in the shape a branch consumes: the unsaturated arm
proves anything, in particular the registered target. -/
theorem target92 {previous : Previous}
    (residual : profile.TypeAResidual previous)
    (negative : NegativeCharge86 profile residual)
    (discharge : Discharge91 profile residual) {Motive : Prop} : Motive :=
  absurd trivial (fun _ => contradiction92 profile residual negative discharge)

end Hypostructure.Graph.Strategy.TypeAReceiverStages

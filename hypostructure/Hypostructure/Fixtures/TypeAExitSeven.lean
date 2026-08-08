import Hypostructure.Graph.Strategy.TypeAExitRun
import Hypostructure.Graph.Strategy.Route8Run

/-!
# Fixture: node `[107]`, exit `(7)` of the saturated exit chain

Exit `(7)` of `def:typeA-saturated-exits` — *"a high-degree decorated handoff
fan envelope is produced"* — is quantified over the keys it consumes and
commits.  This fixture installs it at the spine's *own* vocabulary, on the
ledger the saturated exit chain leaves, and checks the four things the audit's
Ledger, Transport, Residual and Facts columns claim:

* the question elaborates only as a `Decision` against the literal incoming
  branch cursor, in its Figure 8 position inside `Spine.runRouteEight` — after
  node `[105]`'s no arm and before node `[109]` — and only where the shared exit
  segment's entry fact, node `[1]`'s selection and node `[14]`'s hereditary
  target-uncompressibility are all on the index;
* the arm not taken is absent from the taken branch's key index, so node `[109]`
  cannot read the handoff and the Type B entry cannot read the
  exit-`(7)`-free hypothesis;
* **neither** arm carries a closure key: exit `(7)` is the one exit of the list
  that does not close, and the audit's Transport column is about a transfer, not
  a terminal;
* the audit of each exit accounts for the whole branch fact index, with no
  duplicate and no empty commit.

It also exercises, directly at the framework level, the graph statements the row
rests on: the degree bound `d_G(z) ≥ 3` at a separation and `d_G(z) ≥ 4` at a
surviving one (`lem:typeA-cubic-switch-absorption`), the geometric clause of
`def:typeB-fan-safe` (a fan return closes an accepted cycle through the centre),
and the exact-transfer identity of `lem:decorated-envelope-no-double-count`
together with `lem:window-handoff-center-accounting`.

Nothing here is specific to one manuscript: the row runs at the framework's own
`Spine.Data`, left as a parameter, and the graph-level checks quantify over an
arbitrary object, support, port and accepted-length predicate.
-/

namespace Hypostructure.Fixtures.TypeAExitSeven

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The cursor the saturated exit chain leaves -/

/-- The index the shared exit segment is entered on from Figure 8's visible
path: node `[93]`'s port with exits `(1)`, `(2)` and `(3)` denied, and
`lem:typeA-exit4-residual-routing`'s hypothesis committed on node `[99]`'s no
arm.  Nodes `[101]`--`[107]` are asked on top of it. -/
abbrev entryKeys : FactKeys (Input BranchState Presentation presentation data) :=
  saturatedExitEntryKeys (typeAVisibleEntryKeys (BranchState := BranchState)
    (presentation := presentation) (data := data))

/-! ## Node `[107]`, in its Figure 8 position

Figure 8 draws one segment `[101]`--`[107]` entered from node `[99]`'s no arm
and from node `[94]`.  `lem:typeA-exit4-residual-routing` is the manuscript's
statement that the two combine, and `typeASaturatedExitEntry` is its hypothesis.
Node `[107]` is a node of that one segment, asked on node `[105]`'s no arm and
answered before node `[109]`'s placement, so there is no separate runner for it:
the check below is that the *same* ladder `Spine.runRouteEight` that
`Fixtures.Route8Run` runs on node `[94]` also elaborates here, on node `[99]`'s
no arm, with exit `(7)` inside it.

Its three requirements are discharged by instance resolution against the
incoming index — the segment's entry fact, and the selection and
uncompressibility on the standing prefix every branch of the spine carries — and
both freshness side conditions are decided on the vocabulary's own finite
`Key`. -/
noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected entryKeys) :
    Route8Result selected entryKeys :=
  runRouteEight history (peelFresh := by simp) (noPeelFresh := by simp)
    (peeledChargeFresh := by simp) (compressionFresh := by simp)
    (traceLevelFresh := by simp) (exitFourFresh := by simp)
    (exitFourFreeFresh := by simp) (exitFiveFresh := by simp)
    (exitFiveFreeFresh := by simp) (exitSixFresh := by simp)
    (exitSixFreeFresh := by simp) (exitSixProperFresh := by simp)
    (exitSixGlobalFresh := by simp) (exitSevenHandoffFresh := by simp)
    (exitSevenFreeFresh := by simp) (residualFresh := by simp)
    (freeFresh := by simp) (burdenFresh := by simp) (coreFresh := by simp)
    (censusFresh := by simp) (descentFresh := by simp) (closedFresh := by simp)
    (closureFresh := by simp)

/-- **The whole of Figure 8's visible path runs from node `[93]`'s own cursor.**

`[95]` → `[97]` → `[99]` → `[101]` → `[103]` → `[105]` → `[107]` → `[109]` →
`[124]`, walked in one piece.  This is what makes the freshness conditions above
statements about the chain rather than about a chosen cursor: each one is
decided against the index the previous node actually leaves. -/
noncomputable def runVisiblePath
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected typeAVisibleEntryKeys) :
    SaturatedExitResult selected typeAVisibleEntryKeys :=
  runSaturatedExits history (returnFresh := by simp) (oneFreeFresh := by simp)
    (thetaFresh := by simp) (twoFreeFresh := by simp)
    (collisionFresh := by simp) (threeFreeFresh := by simp)
    (entryFresh := by simp) (peelFresh := by simp) (noPeelFresh := by simp)
    (peeledChargeFresh := by simp) (compressionFresh := by simp)
    (traceLevelFresh := by simp) (exitFourFresh := by simp)
    (exitFourFreeFresh := by simp) (exitFiveFresh := by simp)
    (exitFiveFreeFresh := by simp) (exitSixFresh := by simp)
    (exitSixFreeFresh := by simp) (exitSixProperFresh := by simp)
    (exitSixGlobalFresh := by simp) (exitSevenHandoffFresh := by simp)
    (exitSevenFreeFresh := by simp) (residualFresh := by simp)
    (freeFresh := by simp) (burdenFresh := by simp) (coreFresh := by simp)
    (censusFresh := by simp) (descentFresh := by simp) (closedFresh := by simp)
    (closureFresh := by simp)

/-- **Figure 8's branch runs from the spine's own root.**

`Spine.runWithSaturatedExits` calls `Spine.run` once and continues both of its
saturated Type A arms into the exit list: node `[93]`'s yes arm walks
`[95]`--`[124]`, and node `[94]` enters the shared segment at node `[101]`.
This is the check that the branch is attached, not merely elaborable on a
hand-supplied cursor. -/
noncomputable def runAttached
    (T : Core.Target
      (Hypostructure.Graph.Strategy.Spine.problem BranchState Presentation
        presentation data))
    (targetPredicate :
      T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (opened : Core.Strategy.OpenedScope
      (P := Hypostructure.Graph.Strategy.Spine.problem BranchState Presentation
        presentation data) (K .selection))
    (sufficientlyLarge :
      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold
        data.dischargeScale data.windowOrder data.windowRate data.spineScale
        opened.selected.object.vertexCount) :
    SpineWithExitsResult opened.selected :=
  runWithSaturatedExits T targetPredicate opened sufficientlyLarge

/-! ## What the two exits carry -/

/-- **The two arms of node `[107]` are distinct branches.**  Neither index
contains the other's key. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitSevenFree) ∉
      exitSevenHandoffKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitSevenHandoff) ∉
      exitFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-- **Neither arm carries a closure key.**  Exit `(7)` is the one exit of
`def:typeA-saturated-exits` that neither closes nor stays in Type A: the handoff
arm is an open residual that leaves the Type A charge calculation, and the free
arm is the entry of node `[109]`. -/
example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∉
      exitSevenHandoffKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (closed (BranchState := BranchState) (presentation := presentation)
        (data := data)) ∉
      exitFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-- **Both arms still carry node `[93]`'s port and the earlier exits'
hypotheses.**  The exit list is a walk on one prefix. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleEntry) ∈
      exitSevenHandoffKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitThreeFree) ∈
      exitFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-- **The two facts the admissibility spends are on both arms**, and they were
read rather than assumed: node `[1]`'s selection and node `[14]`'s hereditary
target-uncompressibility. -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .selection) ∈
      exitSevenHandoffKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .uncompressible) ∈
      exitSevenHandoffKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-- **The earlier exits' sibling arms are on neither arm of node `[107]`.** -/
example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitOneReturn) ∉
      exitFreeKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAExitThreeCollision) ∉
      exitSevenHandoffKeys (BranchState := BranchState)
        (presentation := presentation) (entryKeys (data := data)) := by
  simp

/-! ## The graph statements the row rests on

All of them are checked at an arbitrary object, support, port and
accepted-length predicate: none knows a degree, a baseline, or a forbidden gap
set. -/

open Hypostructure.Graph.DecoratedHandoff

/-- **`d_G(z) ≥ 3` at any separation.**  The root incidence and the two next
incidences are three distinct neighbours of the separator; the `3` is the number
of incidences the configuration uses, not a registered baseline. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (receiver outside : object.Vertex)
    (separation : Separation object support receiver outside) :
    3 ≤ object.degree separation.separator :=
  separation.three_le_degree

/-- **`lem:typeA-cubic-switch-absorption`.**  A surviving first separator has
ambient degree at least `4`: at degree exactly `3` the separator has no unused
ambient incidence, and `lem:context-universality` then makes the three absorbed
alternatives exhaustive. -/
example (object : Graph.FiniteObject.{u}) (support : Finset object.Vertex)
    (receiver outside : object.Vertex)
    (separation : Separation object support receiver outside)
    {Target : Graph.FiniteObject.{u} → Prop}
    (reading : SwitchReading separation)
    (Enlarges : Prop) (surviving : Surviving Target reading Enlarges) :
    3 < object.degree separation.separator :=
  four_le_degree_of_surviving surviving

/-- **The geometric clause of `def:typeB-fan-safe`.**  *"Any return from `a` to
`b` in `G − h` of length `2^j − 2` would close with the two edges `ha, hb` to
form a cycle of length `2^j`."*  So on an object that carries no accepted cycle
every assigned pair passes the clause. -/
example (object : Graph.FiniteObject.{u}) (LengthOK : Nat → Prop)
    (centre first second : object.Vertex)
    (firstAdj : object.graph.Adj centre first)
    (secondAdj : object.graph.Adj centre second)
    (different : first ≠ second)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    ∀ return' : FanReturn object centre first second,
      ¬ LengthOK (return'.walk.length + 2) :=
  fanSafe_geometric firstAdj secondAdj different avoids

/-- **`lem:decorated-envelope-no-double-count`.**  Summed over the incidence
components, the grouped envelope charges are the Type A core contributions less
the center tokens: each core deficiency is counted once and each ambient
handoff-center token is counted once, so a negative Type A handoff contribution
is transferred rather than discarded. -/
example {Core Component : Type v} [DecidableEq Core] [DecidableEq Component]
    (grouped : GroupedEnvelopes Core Component) (dischargeScale : Nat) :
    ∑ component ∈ grouped.components,
        grouped.componentCharge dischargeScale component =
      ((dischargeScale : Int) *
            (∑ core ∈ grouped.cores, grouped.deficiency core : Nat) -
          (∑ core ∈ grouped.cores, grouped.size core : Nat)) -
        (dischargeScale : Int) *
          (∑ component ∈ grouped.components,
            grouped.componentTokens component : Nat) :=
  grouped.sum_componentCharge dischargeScale

/-- **`lem:window-handoff-center-accounting`.**  A handoff center's own surplus
token is one of the center tokens of the incidence component containing it, so
the grouped envelope containing it is charged to that token — the second
alternative of the manuscript's disjunction, proved outright. -/
example {Core Component : Type v} [DecidableEq Core] [DecidableEq Component]
    (grouped : GroupedEnvelopes Core Component) (Collision : Prop)
    {centre : Component} (member : centre ∈ grouped.centres) :
    Collision ∨
      grouped.token centre ≤
        grouped.componentTokens (grouped.centreComponent centre) :=
  grouped.token_le_componentTokens Collision member

/-! ## The audit of each exit -/

theorem handoff_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (exitSevenHandoffKeys entryKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem free_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (exitFreeKeys entryKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem handoff_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (exitSevenHandoffKeys entryKeys)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem free_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (exitFreeKeys entryKeys)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem handoff_audit_commits_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (exitSevenHandoffKeys entryKeys)) :
    (ExactLedger.audit history).commits.Forall fun record =>
      record.produced ≠ [] :=
  ExactLedger.audit_commits_nonempty history

end Hypostructure.Fixtures.TypeAExitSeven

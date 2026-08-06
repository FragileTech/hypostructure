import Hypostructure.Graph.Strategy.Route8Rows
import Hypostructure.Graph.Strategy.TypeAExitRun

/-!
# The route-8 carrier closure, run

The rows of `Route8Rows` are each quantified over the keys they consume and
produce.  This module installs them at the spine's own vocabulary and runs them
in the manuscript's order against the one canonical `ExactLedger`: the exit-`(4)`
dichotomy of node `[101]`, the exit-`(5)` dichotomy of node `[103]`, the
exit-`(6)` dichotomy of node `[105]`, the exit-`(7)` dichotomy of node `[107]`,
the arm
placement of node `[109]`, the burden and large-budget deficit of
`[111]`--`[113]`, the carrier core of `[114]`--`[116]`, the private-carrier
census of `[117]`--`[122]`, the pressure descent of `[123]`, and the terminal
no-go of `[124]`.

The four exit dichotomies come first, as Figure 8 places them: the arm is
entered only on their no arms, so exits `(4)`--`(7)` of (R2) of
`def:typeA-true-route8-residual` are four facts on the ledger rather than a
clause anyone assumes.  Their yes arms leave the block -- `[101]`'s to the
manuscript's target-defect peel, `[103]`'s to the uncompressibility
contradiction, `[105]`'s to the terminal `[106]`,
whose two cases are `lem:proper-smearing` and `lem:no-silent-global-smearing`,
and `[107]`'s to node `[108]`, which returns the branch to the Type B handoff
-- and carry no route-8 fact.  Exit `(7)`'s yes arm is the one of the four that
is not a terminal: `lem:typeA-saturated-handoff` transfers it out of the Type A
charge calculation, so it leaves the block as an open residual carrying
`lem:decorated-fan-admissibility`'s interface.

Inside the arm the wiring is the manuscript's: `[111]`--`[113]` reads the
`[109]` collection, `[123]` reads `[122]`'s census, and `[124]` reads `[113]`,
`[116]`, `[123]`, `[101]` and `[103]`.  The two collapse rows -- `[114]`--`[116]`
and `[117]`--`[122]` -- are theorems about every route-8 collection of the
object and honestly declare no prerequisite.

The closure is not an assertion: node `[124]` commits that the object carries no
large-budget route-8 collection, and node `[109]` committed that it carries one,
so the canonical closure key is appended by `closeIncompatible` from the two
facts themselves.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The rows, at the spine's own keys

Every schema bridge below is the identity on `PLift`: the spine's value at a
route-8 key *is* the manuscript statement, so nothing is re-encoded. -/

/-- Nodes `[111]`--`[113]`: the burden and the large-budget deficit. -/
@[reducible] noncomputable def route8Burden :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  route8BurdenRow (K .route8Residual) (K .route8Burden) (by simp)
    (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Nodes `[114]`--`[116]`: the essential carrier core. -/
@[reducible] noncomputable def route8CarrierCore :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  route8CarrierCoreRow (K .route8CarrierCore) (fun _input value => ⟨value⟩)

/-- Nodes `[117]`--`[122]`: the private-carrier census. -/
@[reducible] noncomputable def route8Census :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  route8CensusRow (K .route8Census) (fun _input value => ⟨value⟩)

/-- Node `[123]`: the pressure descent. -/
@[reducible] noncomputable def route8Descent :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  route8DescentRow (K .route8Census) (K .route8Descent) (by simp)
    (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Node `[124]`: the terminal two-carrier no-go. -/
@[reducible] noncomputable def route8Closed :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  route8ClosedRow (K .route8Burden) (K .route8CarrierCore) (K .route8Descent)
    (K .typeAExitFourFree) (K .typeAExitFiveFree) (K .route8Closed) (by simp)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input fact => fact.down) (fun _input fact => fact.down)
    (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Node `[102]`: the peeled receiver, returned to node `[89]`. -/
@[reducible] noncomputable def typeAPeeledCharge :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeAPeeledChargeRow (K .typeAExitFourPeel) (K .typeAPeeledCharge) (by simp)
    (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-! ## The closure of the arm -/

/-- **Exit `(5)` realized by a smaller proper atom is impossible.**

Node `[103]`'s yes arm carries `lem:replacement`'s target-complete compression of
a proper support; node `[14]`'s `cor:uncompressible` says the object has none.
That is the manuscript's *"if the compression is realized by a smaller proper
atom, it contradicts hereditary target-uncompressibility"*, and it is read off
the two committed statements. -/
noncomputable instance typeAExitFiveCompressionClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .uncompressible)
      (K (data := data) .typeAExitFiveCompression) where
  contradiction := fun _input uncompressible compression =>
    let ⟨support, compressible⟩ := compression.down
    uncompressible.down support compressible

/-- **A proper delocalization support is impossible.**

Node `[105]`'s scope test, proper arm, carries `lem:proper-smearing`'s
conclusion: the equality that becomes target-complete only after adjoining
`Z ⊋ B_u` with `Z ⊊ G` makes `Z` a replacement of a proper boundaried support.
`lem:replacement` and `cor:uncompressible` forbid one at the selected minimal
counterexample, which is what `not_globalBarrierReading` refutes on its first
disjunct.  The collision is between the arm's fact and the selection's own
avoidance and minimality, so it is read off two committed statements. -/
noncomputable instance typeAExitSixProperClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection) (K (data := data) .typeAExitSixProper) where
  contradiction := fun residual selected proper => by
    obtain ⟨_support, replacement⟩ := proper.down
    exact not_globalBarrierReading residual.baseline residual.branchState
      selected.down.1 selected.down.2 (Or.inl replacement)

/-- **A whole-graph delocalization is impossible.**

Node `[105]`'s scope test, global arm, carries
`lem:no-silent-global-smearing`'s conclusion: the whole-graph dependence
supplies a strictly smaller admissible closed representative.  The selection
says every strictly smaller baseline object realizes the target and that the
selected object does not, so the representative transfers a target the object
avoids.  Nothing is recomputed: both halves come from the two facts. -/
noncomputable instance typeAExitSixGlobalClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection) (K (data := data) .typeAExitSixGlobal) where
  contradiction := fun _residual selected global => by
    obtain ⟨representative, smaller, baseline, transfer⟩ := global.down
    exact selected.down.1
      (transfer (selected.down.2 representative smaller baseline))

/-- **The two route-8 facts are incompatible.**

Node `[109]` commits that the object carries a large-budget route-8 collection
and node `[124]` commits that it carries none.  Neither fact mentions the other,
and neither row knows the other exists: the contradiction is read off the two
committed statements, which is what makes the closure the framework's rather
than a row's. -/
noncomputable instance route8ResidualClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .route8Residual) (K (data := data) .route8Closed) where
  contradiction := fun _input carried empty => empty.down carried.down

/-! ## The block, run -/

/-- The key index of node `[101]`'s ladder arm: the peel step and the peeled
receiver of node `[102]`, which the manuscript returns to node `[89]`. -/
abbrev peeledKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAPeeledCharge :: K .typeAExitFourPeel :: known

/-- The key index of node `[103]`'s closed arm: the compression realized by a
smaller proper atom, closed against node `[14]`. -/
abbrev exitFiveClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeAExitFiveCompression :: K .typeAExitFive ::
    K .typeAExitFourFree :: K .typeAExitFourNoPeel :: known

/-- The key index of node `[103]`'s response-level arm: alternative (b) of
`def:typeA-trace-basin`, which is not an admissible route-8 residual. -/
abbrev exitFiveTraceLevelKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFiveTraceLevel :: K .typeAExitFive :: K .typeAExitFourFree ::
    K .typeAExitFourNoPeel :: known

/-- The key index of node `[103]`'s no arm — the entry of node `[105]`. -/
abbrev exitFiveFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFiveFree :: K .typeAExitFourFree :: K .typeAExitFourNoPeel :: known

/-- The key index of node `[105]`'s proper arm: `lem:proper-smearing`'s
replacement of the enlarging support, closed against the selection. -/
abbrev exitSixProperKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeAExitSixProper :: K .typeAExitSix :: exitFiveFreeKeys known

/-- The key index of node `[105]`'s global arm:
`lem:no-silent-global-smearing`'s smaller admissible closed representative,
closed against the selection. -/
abbrev exitSixGlobalKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeAExitSixGlobal :: K .typeAExitSix :: exitFiveFreeKeys known

/-- The key index of nodes `[101]`, `[103]` and `[105]`'s no arms — the cursor
node `[107]` is asked on. -/
abbrev exitSixFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSixFree :: exitFiveFreeKeys known

/-- The key index of node `[107]`'s yes arm: the admissible decorated handoff
fan envelope node `[108]` returns to the Type B handoff.  There is no closure
key — exit `(7)` is the one exit of `def:typeA-saturated-exits` that neither
closes nor stays in Type A. -/
abbrev exitSevenHandoffKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSevenHandoff :: exitSixFreeKeys known

/-- The key index of nodes `[101]`, `[103]`, `[105]` and `[107]`'s no arms:
exits `(4)`--`(7)` of (R2) of `def:typeA-true-route8-residual`. -/
abbrev exitFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSevenFree :: exitSixFreeKeys known

/-- The key index a branch carries after the five rows of the route-8 arm. -/
abbrev route8Keys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .route8Closed :: K .route8Descent :: K .route8Census ::
    K .route8CarrierCore :: K .route8Burden :: K .route8Residual ::
    exitFreeKeys known

/-- The key index of node `[101]`'s route-8 `(Q5)` arm. -/
abbrev exitFourKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFour :: K .typeAExitFourNoPeel :: known

/-- The key index of the closed route-8 terminal. -/
abbrev route8ClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: route8Keys known

/-- The key index of the branch that carries no route-8 residual. -/
abbrev route8FreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .route8Free :: exitFreeKeys known

/-- **The exits of the route-8 block.**

`exitFour` and `exitFive` are the yes arms of nodes `[101]` and `[103]`, which
leave the block; `exitSixProper` and `exitSixGlobal` are the two cases of node
`[105]`'s terminal `[106]`, each closed against the selection;
`exitSevenHandoff` is node `[107]`'s yes arm, which node `[108]` returns to the
Type B handoff and which is an *open* residual rather than a terminal; `free` is
node `[109]`'s complementary arm, which carries no route-8 collection; `closed`
is Figure 9's terminal, with Core's closure key appended from the two
incompatible facts. -/
inductive Route8Result
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | peeled
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (peeledKeys known))
  | exitFour
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (exitFourKeys known))
  | exitFiveClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (exitFiveClosedKeys known))
  | exitFiveTraceLevel
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (exitFiveTraceLevelKeys known))
  | exitSixProper
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (exitSixProperKeys known))
  | exitSixGlobal
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (exitSixGlobalKeys known))
  | exitSevenHandoff
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (exitSevenHandoffKeys known))
  | free
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (route8FreeKeys known))
  | closed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (route8ClosedKeys known))

set_option maxHeartbeats 1600000 in
/-- **The route-8 carrier closure, run.**

The five decisions commit one arm each; on the arm that carries a collection the
five rows are composed by `AtomicCT.run`, which appends each row's declared
productions to the incoming index while retaining the literal ancestry.  Every
prerequisite is discharged by instance resolution against the incoming index --
node `[113]` does not elaborate before the `[109]` residual, node `[123]` does
not elaborate before the census, and the terminal does not elaborate before all
three of `[113]`, `[116]` and `[123]` -- and every freshness side condition is
decided on the vocabulary's own finite `Key`. -/
noncomputable def runRouteEight
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .typeASaturatedExitEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (peelFresh : K (data := data) .typeAExitFourPeel ∉ known)
    (noPeelFresh : K (data := data) .typeAExitFourNoPeel ∉ known)
    (peeledChargeFresh : K (data := data) .typeAPeeledCharge ∉ known)
    (compressionFresh : K (data := data) .typeAExitFiveCompression ∉ known)
    (traceLevelFresh : K (data := data) .typeAExitFiveTraceLevel ∉ known)
    (exitFourFresh : K (data := data) .typeAExitFour ∉ known)
    (exitFourFreeFresh : K (data := data) .typeAExitFourFree ∉ known)
    (exitFiveFresh : K (data := data) .typeAExitFive ∉ known)
    (exitFiveFreeFresh : K (data := data) .typeAExitFiveFree ∉ known)
    (exitSixFresh : K (data := data) .typeAExitSix ∉ known)
    (exitSixFreeFresh : K (data := data) .typeAExitSixFree ∉ known)
    (exitSixProperFresh : K (data := data) .typeAExitSixProper ∉ known)
    (exitSixGlobalFresh : K (data := data) .typeAExitSixGlobal ∉ known)
    (exitSevenHandoffFresh : K (data := data) .typeAExitSevenHandoff ∉ known)
    (exitSevenFreeFresh : K (data := data) .typeAExitSevenFree ∉ known)
    (residualFresh : K (data := data) .route8Residual ∉ known)
    (freeFresh : K (data := data) .route8Free ∉ known)
    (burdenFresh : K (data := data) .route8Burden ∉ known)
    (coreFresh : K (data := data) .route8CarrierCore ∉ known)
    (censusFresh : K (data := data) .route8Census ∉ known)
    (descentFresh : K (data := data) .route8Descent ∉ known)
    (closedFresh : K (data := data) .route8Closed ∉ known)
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    Route8Result current known := by
  classical
  -- Node `[101]`, the ladder's peel test.
  match typeAExitFourPeelDichotomy history (K .typeASaturatedExitEntry)
      (K .typeAExitFourPeel) (K .typeAExitFourNoPeel) (fun fact => fact.down)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩) peelFresh noPeelFresh with
  | .left available =>
      -- Node `[102]`: peel to a nonnegative charge and return to node `[89]`.
      exact .peeled
        ((typeAPeeledCharge (data := data)).run available (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [peeledChargeFresh]))
  | .right noPeel =>
  -- Node `[101]`, the route-8 `(Q5)` reading.
  match typeAExitFourDichotomy noPeel (K .typeASaturatedExitEntry)
      (K .typeAExitFour) (K .typeAExitFourFree) (fun fact => fact.down)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩) (by simp [exitFourFresh])
      (by simp [exitFourFreeFresh]) with
  | .left carrierExit => exact .exitFour carrierExit
  | .right exitFourFree =>
  -- Node `[103]`: exit `(5)`.
  match typeAExitFiveDichotomy exitFourFree (K .typeASaturatedExitEntry)
      (K .typeAExitFive) (K .typeAExitFiveFree) (fun fact => fact.down)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [exitFiveFresh]) (by simp [exitFiveFreeFresh]) with
  | .left compressed =>
      -- Node `[103]`, the realization test of `lem:typeA-exits-discharged`.
      match typeAExitFiveRealizationDichotomy compressed
          (K .typeAExitFiveCompression) (K .typeAExitFiveTraceLevel)
          (fun value => ⟨value⟩) (fun value => ⟨value⟩)
          (by simp [compressionFresh]) (by simp [traceLevelFresh]) with
      | .left realized =>
          exact .exitFiveClosed
            (closeIncompatible realized (K .uncompressible)
              (K .typeAExitFiveCompression) (by simp [closureFresh]))
      | .right traceLevel => exact .exitFiveTraceLevel traceLevel
  | .right surviving =>
  -- Node `[105]`: exit `(6)`, clause (c) of `def:typeA-trace-basin`.
  match typeAExitSixDichotomy surviving (K .typeASaturatedExitEntry)
      (K .typeAExitSix) (K .typeAExitSixFree) (fun fact => fact.down)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [exitSixFresh]) (by simp [exitSixFreeFresh]) with
  | .left delocalized =>
      -- Node `[105]`, the scope test of `lem:typeA-exits-discharged`.
      match typeAExitSixScopeDichotomy delocalized (K .typeAExitSix)
          (K .typeAExitSixProper) (K .typeAExitSixGlobal)
          (fun fact => fact.down) (fun value => ⟨value⟩)
          (fun value => ⟨value⟩)
          (by simp [exitSixProperFresh]) (by simp [exitSixGlobalFresh]) with
      | .left proper =>
          exact .exitSixProper
            (closeIncompatible proper (K .selection) (K .typeAExitSixProper)
              (by simp [closureFresh]))
      | .right global =>
          exact .exitSixGlobal
            (closeIncompatible global (K .selection) (K .typeAExitSixGlobal)
              (by simp [closureFresh]))
  | .right exitSixFree =>
  -- Node `[107]`: exit `(7)`, clause (d) of `def:typeA-trace-basin`.
  match typeAExitSevenDichotomy exitSixFree (K .selection) (K .uncompressible)
      (K .typeASaturatedExitEntry) (K .typeAExitSevenHandoff)
      (K .typeAExitSevenFree)
      (fun fact => fact.down.1) (fun fact => fact.down) (fun fact => fact.down)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [exitSevenHandoffFresh]) (by simp [exitSevenFreeFresh]) with
  | .left handoff => exact .exitSevenHandoff handoff
  | .right exitSevenFree =>
  -- Node `[109]`: the arm placement, on the ladder's no arms.
  match route8Placement exitSevenFree (K .route8Residual) (K .route8Free)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      (by simp [residualFresh]) (by simp [freeFresh]) with
  | .right free => exact .free free
  | .left carried =>
      -- Nodes `[111]`--`[124]` on the arm that carries a residual.
      have afterBurden :=
        (route8Burden (data := data)).run carried (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [burdenFresh])
      have afterCore :=
        (route8CarrierCore (data := data)).run afterBurden (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [coreFresh])
      have afterCensus :=
        (route8Census (data := data)).run afterCore (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [censusFresh])
      have afterDescent :=
        (route8Descent (data := data)).run afterCensus (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [descentFresh])
      have afterClosed :=
        (route8Closed (data := data)).run afterDescent (by
          intro key isNew isOld
          simp only [List.mem_singleton] at isNew
          subst isNew
          revert isOld
          simp [closedFresh])
      exact .closed
        (closeIncompatible afterClosed (K .route8Residual) (K .route8Closed)
          (by simp [closureFresh]))

/-! ## Figure 8's visible path, walked in one piece

Node `[93]`'s yes arm enters `def:typeA-saturated-exits` at exit `(1)` and
Figure 8 walks the list to the end: `[95]` → `[97]` → `[99]` → `[101]` → `[103]`
→ `[105]` → `[107]` → `[109]`.  `runExitChain` is the first half and
`runRouteEight` is the second; the join is `lem:typeA-unpeeled-visible-routing`,
which routes node `[99]`'s no arm into the shared exit segment, and the fact it
commits there is the segment entry the second half is asked under.

Nothing new is proved here.  The composition is what shows the list really is
one walk on one immutable prefix: every freshness side condition of the second
half is decided against the index the first half actually leaves, rather than
supplied at a chosen cursor. -/

/-- The cursor Figure 8 reaches after exits `(1)`--`(3)` are denied: node
`[99]`'s no arm with the shared segment's entry committed on top. -/
abbrev saturatedExitEntryKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedExitEntry ::
    typeAExitThreeFreeKeys (typeAExitTwoFreeKeys (typeAExitOneFreeKeys known))

/-- **The exits of Figure 8's visible path.**

The first three are the closed terminals `[96]`, `[98]` and `[100]`; `segment`
is everything the shared exit segment `[101]`--`[107]` and the route-8 arm
`[109]`--`[124]` produce, over the cursor node `[99]`'s no arm leaves. -/
inductive SaturatedExitResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | exitOneClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitOneClosedKeys known))
  | exitTwoClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitTwoClosedKeys (typeAExitOneFreeKeys known)))
  | exitThreeClosed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitThreeClosedKeys
          (typeAExitTwoFreeKeys (typeAExitOneFreeKeys known))))
  | segment
      (result : Route8Result selected (saturatedExitEntryKeys known))

set_option maxHeartbeats 1600000 in
/-- **`def:typeA-saturated-exits`, walked from node `[95]` to node `[124]`.**

Exits `(1)`--`(3)` first, then the shared segment `[101]`--`[107]` and the
route-8 arm, in Figure 8's order.  Each block's requirements are discharged by
instance resolution against the index the previous block leaves, and each
block's freshness conditions are decided on the vocabulary's own finite `Key`
against that same index. -/
noncomputable def runSaturatedExits
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .uncompressible) known]
    [FactKeys.Has (K (data := data) .returnAvoidance) known]
    [FactKeys.Has (K (data := data) .typeASaturatedReceiver) known]
    [FactKeys.Has (K (data := data) .typeAVisibleEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (returnFresh : K (data := data) .typeAExitOneReturn ∉ known)
    (oneFreeFresh : K (data := data) .typeAExitOneFree ∉ known)
    (thetaFresh : K (data := data) .typeAExitTwoTheta ∉ known)
    (twoFreeFresh : K (data := data) .typeAExitTwoFree ∉ known)
    (collisionFresh : K (data := data) .typeAExitThreeCollision ∉ known)
    (threeFreeFresh : K (data := data) .typeAExitThreeFree ∉ known)
    (entryFresh : K (data := data) .typeASaturatedExitEntry ∉ known)
    (peelFresh : K (data := data) .typeAExitFourPeel ∉ known)
    (noPeelFresh : K (data := data) .typeAExitFourNoPeel ∉ known)
    (peeledChargeFresh : K (data := data) .typeAPeeledCharge ∉ known)
    (compressionFresh : K (data := data) .typeAExitFiveCompression ∉ known)
    (traceLevelFresh : K (data := data) .typeAExitFiveTraceLevel ∉ known)
    (exitFourFresh : K (data := data) .typeAExitFour ∉ known)
    (exitFourFreeFresh : K (data := data) .typeAExitFourFree ∉ known)
    (exitFiveFresh : K (data := data) .typeAExitFive ∉ known)
    (exitFiveFreeFresh : K (data := data) .typeAExitFiveFree ∉ known)
    (exitSixFresh : K (data := data) .typeAExitSix ∉ known)
    (exitSixFreeFresh : K (data := data) .typeAExitSixFree ∉ known)
    (exitSixProperFresh : K (data := data) .typeAExitSixProper ∉ known)
    (exitSixGlobalFresh : K (data := data) .typeAExitSixGlobal ∉ known)
    (exitSevenHandoffFresh : K (data := data) .typeAExitSevenHandoff ∉ known)
    (exitSevenFreeFresh : K (data := data) .typeAExitSevenFree ∉ known)
    (residualFresh : K (data := data) .route8Residual ∉ known)
    (freeFresh : K (data := data) .route8Free ∉ known)
    (burdenFresh : K (data := data) .route8Burden ∉ known)
    (coreFresh : K (data := data) .route8CarrierCore ∉ known)
    (censusFresh : K (data := data) .route8Census ∉ known)
    (descentFresh : K (data := data) .route8Descent ∉ known)
    (closedFresh : K (data := data) .route8Closed ∉ known)
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    SaturatedExitResult current known := by
  classical
  match runExitChain history returnFresh oneFreeFresh thetaFresh twoFreeFresh
      collisionFresh threeFreeFresh entryFresh closureFresh with
  | .exitOneClosed closedHistory => exact .exitOneClosed closedHistory
  | .exitTwoClosed closedHistory => exact .exitTwoClosed closedHistory
  | .exitThreeClosed closedHistory => exact .exitThreeClosed closedHistory
  | .free entered =>
      exact .segment
        (runRouteEight entered (by simp [peelFresh]) (by simp [noPeelFresh])
          (by simp [peeledChargeFresh]) (by simp [compressionFresh])
          (by simp [traceLevelFresh]) (by simp [exitFourFresh])
          (by simp [exitFourFreeFresh]) (by simp [exitFiveFresh])
          (by simp [exitFiveFreeFresh]) (by simp [exitSixFresh])
          (by simp [exitSixFreeFresh]) (by simp [exitSixProperFresh])
          (by simp [exitSixGlobalFresh]) (by simp [exitSevenHandoffFresh])
          (by simp [exitSevenFreeFresh]) (by simp [residualFresh])
          (by simp [freeFresh]) (by simp [burdenFresh]) (by simp [coreFresh])
          (by simp [censusFresh]) (by simp [descentFresh])
          (by simp [closedFresh]) (by simp [closureFresh]))

/-! ## Figure 8's branch, attached to `Spine.run`

`Spine.run` reaches node `[93]`'s yes arm and node `[94]`; Figure 8 continues
both into the saturated exit list.  The visible arm enters at exit `(1)` and
walks `[95]`--`[124]`; the silent arm is routed by
`lem:typeA-unpeeled-silent-routing` straight into the shared segment, so it
already carries `typeASaturatedExitEntry` and enters the ladder at node `[101]`.

Nothing here is a second copy of the spine: `Spine.run` is called once and its
other arms are passed through unchanged. -/

/-- **The spine, with Figure 8's saturated exit list attached.**

`visibleExits` is node `[93]`'s yes arm continued through
`Spine.runSaturatedExits`, `silentExits` is node `[94]` continued through
`Spine.runRouteEight`, and `spine` is every arm of `Spine.run` that does not
reach the saturated Type A branch. -/
inductive SpineWithExitsResult
    (selected : Input BranchState Presentation presentation data) where
  | spine (result : Result selected)
  | visibleExits
      (result : SaturatedExitResult selected
        (typeAVisibleEntryKeys (BranchState := BranchState)
          (presentation := presentation) (data := data)))
  | silentExits
      (result : Route8Result selected
        (typeAVisibleFirstExcessKeys (BranchState := BranchState)
          (presentation := presentation) (data := data)))

set_option maxHeartbeats 3200000 in
/-- **Block A, run, with Figure 8's exit list attached.**

The two saturated Type A arms of `Spine.run` are continued into the exit list
in Figure 8's own order; every other arm is returned as it stands.  Each
continuation's requirements are discharged by instance resolution against the
index `Spine.run` actually leaves, and every freshness side condition is decided
on the vocabulary's own finite `Key`. -/
noncomputable def runWithSaturatedExits
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (opened : OpenedScope
      (P := problem BranchState Presentation presentation data) (K .selection)) :
    SpineWithExitsResult opened.selected := by
  classical
  match Spine.run T targetPredicate opened with
  | .typeAVisibleEntry visible =>
      exact .visibleExits
        (runSaturatedExits visible (returnFresh := by simp)
          (oneFreeFresh := by simp) (thetaFresh := by simp)
          (twoFreeFresh := by simp) (collisionFresh := by simp)
          (threeFreeFresh := by simp) (entryFresh := by simp)
          (peelFresh := by simp) (noPeelFresh := by simp)
          (peeledChargeFresh := by simp) (compressionFresh := by simp)
          (traceLevelFresh := by simp) (exitFourFresh := by simp)
          (exitFourFreeFresh := by simp) (exitFiveFresh := by simp)
          (exitFiveFreeFresh := by simp) (exitSixFresh := by simp)
          (exitSixFreeFresh := by simp) (exitSixProperFresh := by simp)
          (exitSixGlobalFresh := by simp) (exitSevenHandoffFresh := by simp)
          (exitSevenFreeFresh := by simp) (residualFresh := by simp)
          (freeFresh := by simp) (burdenFresh := by simp) (coreFresh := by simp)
          (censusFresh := by simp) (descentFresh := by simp)
          (closedFresh := by simp) (closureFresh := by simp))
  | .typeAVisibleFirstExcess silent =>
      exact .silentExits
        (runRouteEight silent (peelFresh := by simp) (noPeelFresh := by simp)
          (peeledChargeFresh := by simp) (compressionFresh := by simp)
          (traceLevelFresh := by simp) (exitFourFresh := by simp)
          (exitFourFreeFresh := by simp) (exitFiveFresh := by simp)
          (exitFiveFreeFresh := by simp) (exitSixFresh := by simp)
          (exitSixFreeFresh := by simp) (exitSixProperFresh := by simp)
          (exitSixGlobalFresh := by simp) (exitSevenHandoffFresh := by simp)
          (exitSevenFreeFresh := by simp) (residualFresh := by simp)
          (freeFresh := by simp) (burdenFresh := by simp) (coreFresh := by simp)
          (censusFresh := by simp) (descentFresh := by simp)
          (closedFresh := by simp) (closureFresh := by simp))
  | other => exact .spine other

end Hypostructure.Graph.Strategy.Spine

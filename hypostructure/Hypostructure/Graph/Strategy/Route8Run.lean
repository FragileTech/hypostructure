import Hypostructure.Graph.Strategy.Route8Rows
import Hypostructure.Graph.Strategy.SpineRun

/-!
# The route-8 carrier closure, run

The rows of `Route8Rows` are each quantified over the keys they consume and
produce.  This module installs them at the spine's own vocabulary and runs them
in the manuscript's order against the one canonical `ExactLedger`: the exit-`(4)`
dichotomy of node `[101]`, the exit-`(5)` dichotomy of node `[103]`, the arm
placement of node `[109]`, the burden and large-budget deficit of
`[111]`--`[113]`, the carrier core of `[114]`--`[116]`, the private-carrier
census of `[117]`--`[122]`, the pressure descent of `[123]`, and the terminal
no-go of `[124]`.

The two exit dichotomies come first, as Figure 8 places them: the arm is entered
only on their no arms, so (R2) of `def:typeA-true-route8-residual` is two facts
on the ledger rather than a clause anyone assumes.  Their yes arms leave the
block -- `[101]`'s to the manuscript's target-defect peel and `[103]`'s to the
uncompressibility contradiction -- and carry no route-8 fact.

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

/-- The key index of nodes `[101]` and `[103]`'s no arms: (R2). -/
abbrev exitFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFiveFree :: K .typeAExitFourFree :: K .typeAExitFourNoPeel :: known

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
leave the block; `free` is node `[109]`'s complementary arm, which carries no
route-8 collection; `closed` is Figure 9's terminal, with Core's closure key
appended from the two incompatible facts. -/
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
  | free
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (route8FreeKeys known))
  | closed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (route8ClosedKeys known))

set_option maxHeartbeats 800000 in
/-- **The route-8 carrier closure, run.**

The three decisions commit one arm each; on the arm that carries a collection the
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
  match typeAExitFourPeelDichotomy history (K .typeAExitFourPeel)
      (K .typeAExitFourNoPeel) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
      peelFresh noPeelFresh with
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
  match typeAExitFourDichotomy noPeel (K .typeAExitFour) (K .typeAExitFourFree)
      (fun value => ⟨value⟩) (fun value => ⟨value⟩) (by simp [exitFourFresh])
      (by simp [exitFourFreeFresh]) with
  | .left carrierExit => exact .exitFour carrierExit
  | .right exitFourFree =>
  -- Node `[103]`: exit `(5)`.
  match typeAExitFiveDichotomy exitFourFree (K .typeAExitFive)
      (K .typeAExitFiveFree) (fun value => ⟨value⟩) (fun value => ⟨value⟩)
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
  -- Node `[109]`: the arm placement, on the ladder's no arms.
  match route8Placement surviving (K .route8Residual) (K .route8Free)
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

end Hypostructure.Graph.Strategy.Spine

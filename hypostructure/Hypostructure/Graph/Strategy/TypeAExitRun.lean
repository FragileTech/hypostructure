import Hypostructure.Graph.Strategy.SpineRows

/-!
# The saturated exit chain, run: node `[95]`

Node `[93]`'s yes arm enters `def:typeA-saturated-exits`, and its first
alternative is exit `(1)`: *"an anchored return through a completion port of `w`
has length in `Mers`"*.  This module installs that question at the spine's own
vocabulary and runs it against the one canonical `ExactLedger`.

The row is quantified over the keys it consumes and produces, so the runner
below asks it after *any* canonical branch cursor whose index already carries
node `[93]`'s visible-entry fact and the return-avoidance invariant of nodes
`[5]`--`[7]`.  It names no producer, no execution position and no predecessor
depth: both requirements are discharged by instance resolution against the
incoming index.

The yes arm is closed, and the closure is not this block's assertion.
`lem:typeA-exits-discharged` says exit `(1)` *"gives an edge-rooted Mersenne
return, hence a power-of-two cycle by `lem:return-equivalence`"*; nodes
`[5]`--`[7]` committed that every oriented edge's return-length set misses the
shifted accepted set.  Neither fact mentions the other and neither row knows the
other exists, so Core's own `closeIncompatible` appends the closure key from the
two committed statements.

The no arm carries the hypothesis exit `(2)` is asked under at node `[97]`: no
anchored return through any completion port of any saturated receiver has
accepted length.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The row, at the spine's own keys

The schema bridges are the identity on `PLift`: the spine's value at each
exit-`(1)` key *is* the manuscript statement, so nothing is re-encoded. -/

/-- **Node `[95]`, asked on node `[93]`'s cursor.**

The visible-entry requirement is discharged by instance resolution against the
incoming index, so this question does not elaborate on a history that has not
entered the saturated exit chain. -/
noncomputable def typeAExitOne
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .typeAVisibleEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (returnFresh : K (data := data) .typeAExitOneReturn ∉ known)
    (freeFresh : K (data := data) .typeAExitOneFree ∉ known) :
    Decision (K (data := data) .typeAExitOneReturn)
      (K (data := data) .typeAExitOneFree) history :=
  typeAExitOneDichotomy history (K .typeAVisibleEntry) (K .typeAExitOneReturn)
    (K .typeAExitOneFree) (fun fact => fact.down) (fun value => ⟨value⟩)
    (fun value => ⟨value⟩) returnFresh freeFresh

/-! ## The closure of the yes arm -/

/-- **An accepted anchored return through a completion port is impossible on
this branch.**

Exit `(1)` says some anchored return through a completion port of a saturated
receiver has length in `Mers`.  Restoring the port edge over that return closes
a simple cycle one longer — `lem:return-equivalence` at the port's own oriented
edge — and nodes `[5]`--`[7]` committed that no oriented edge of the selected
object carries a return of shifted-accepted length.  The contradiction is read
off the two committed statements, which is what makes the closure the
framework's rather than a row's. -/
noncomputable instance typeAExitOneReturnClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .returnAvoidance)
      (K (data := data) .typeAExitOneReturn) where
  contradiction := fun _input avoidance exit => by
    obtain ⟨_packing, _valid, _maximal, _piece, _inside, _connected, _charge,
      _surplus, _receiver, _isReceiver, _saturated, _outside, port,
      return', accepted⟩ := exit.down
    exact Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint
      data.LengthOK avoidance.down
      (Graph.VisibleEntry.mem_completionPorts.mp port).1 return' accepted

/-! ## The block, run -/

/-- The key index of node `[95]`'s closed arm: the Mersenne anchored return,
closed against the return-avoidance invariant of nodes `[5]`--`[7]`. -/
abbrev typeAExitOneClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeAExitOneReturn :: known

/-- The key index of node `[95]`'s no arm — the entry of node `[97]`. -/
abbrev typeAExitOneFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitOneFree :: known

/-- **The exits of node `[95]`.**

`closed` is the terminal `lem:typeA-exits-discharged` records for exit `(1)`,
with Core's closure key appended from the two incompatible facts; `free` is the
alternative the saturated exit list continues on at node `[97]`. -/
inductive ExitOneResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | closed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitOneClosedKeys known))
  | free
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitOneFreeKeys known))

/-- **Exit `(1)` of `def:typeA-saturated-exits`, run.**

The decision commits one arm; on the arm that carries the accepted return the
closure key is appended by `closeIncompatible` from node `[95]`'s fact and the
return-avoidance invariant, both read by exact key off the incoming index.
Nothing is transported between the two arms, and the arm not taken is absent
from the taken branch's index. -/
noncomputable def runExitOne
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .returnAvoidance) known]
    [FactKeys.Has (K (data := data) .typeAVisibleEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (returnFresh : K (data := data) .typeAExitOneReturn ∉ known)
    (freeFresh : K (data := data) .typeAExitOneFree ∉ known)
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    ExitOneResult current known := by
  classical
  match typeAExitOne history returnFresh freeFresh with
  | .left realized =>
      exact .closed
        (closeIncompatible realized (K .returnAvoidance) (K .typeAExitOneReturn)
          (by simp [closureFresh]))
  | .right free => exact .free free

/-! ## What the two exits carry -/

theorem exitOneClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneClosedKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitOneFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitOneClosed_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneClosedKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitOneFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitOneFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-! # The saturated exit chain, run: node `[97]`

Exit `(2)` of `def:typeA-saturated-exits`: *"two anchored receiver-entry
returns through one completion port are internally vertex-disjoint as anchored
paths and their lengths sum to a power of two"*.  The chain reaches it on node
`[95]`'s no arm, so the row is asked after a cursor that carries node `[93]`'s
visible-entry fact and node `[95]`'s exit-`(1)`-free hypothesis; as at node
`[95]`, the requirement is discharged by instance resolution against the
incoming index and the row names no producer and no execution position.

The yes arm is closed, and the closure is again not this block's assertion.
`lem:typeA-common-port-return-cycle` glues the two returns into a simple cycle
of length `|P₁| + |P₂|`, and the exit's own side condition says that length is
accepted; node `[1]`'s selection committed that the object carries no accepted
cycle.  Neither fact mentions the other, so Core's `closeIncompatible` appends
the closure key from the two committed statements.

The no arm carries the hypothesis exit `(3)` is asked under at node `[99]`. -/

/-- **Node `[97]`, asked on node `[95]`'s free cursor.** -/
noncomputable def typeAExitTwo
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .typeAVisibleEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (thetaFresh : K (data := data) .typeAExitTwoTheta ∉ known)
    (freeFresh : K (data := data) .typeAExitTwoFree ∉ known) :
    Decision (K (data := data) .typeAExitTwoTheta)
      (K (data := data) .typeAExitTwoFree) history :=
  typeAExitTwoDichotomy history (K .typeAVisibleEntry) (K .typeAExitTwoTheta)
    (K .typeAExitTwoFree) (fun fact => fact.down) (fun value => ⟨value⟩)
    (fun value => ⟨value⟩) thetaFresh freeFresh

/-! ## The closure of the yes arm -/

/-- **An accepted common-port theta is impossible on this branch.**

Exit `(2)` says two receiver-entry returns through one completion port of a
saturated receiver are internally vertex-disjoint with accepted total length.
Both returns run between the port's two ends, so
`lem:typeA-common-port-return-cycle` makes their union a simple cycle of that
length, and node `[1]` selected an object with no accepted cycle.  The
contradiction is read off the two committed statements, which is what makes the
closure the framework's rather than a row's. -/
noncomputable instance typeAExitTwoThetaClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection)
      (K (data := data) .typeAExitTwoTheta) where
  contradiction := fun _input selected exit => by
    obtain ⟨_packing, _valid, _maximal, _piece, _inside, _connected, _charge,
      _surplus, _receiver, _isReceiver, _saturated, _outside, port,
      pair⟩ := exit.down
    exact selected.down.1
      (Graph.VisibleEntry.hasCycleWithLength_of_exitTwoThrough port pair)

/-! ## The block, run -/

/-- The key index of node `[97]`'s closed arm: the common-port theta, closed
against the selection's own avoidance. -/
abbrev typeAExitTwoClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeAExitTwoTheta :: known

/-- The key index of node `[97]`'s no arm — the entry of node `[99]`. -/
abbrev typeAExitTwoFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitTwoFree :: known

/-- **The exits of node `[97]`.**

`closed` is the terminal `lem:typeA-exits-discharged` records for exit `(2)`;
`free` is the alternative the saturated exit list continues on at node
`[99]`. -/
inductive ExitTwoResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | closed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitTwoClosedKeys known))
  | free
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitTwoFreeKeys known))

/-- **Exit `(2)` of `def:typeA-saturated-exits`, run.**

The decision commits one arm; on the arm that carries the theta the closure key
is appended by `closeIncompatible` from node `[97]`'s fact and node `[1]`'s
selection, both read by exact key off the incoming index.  Nothing is
transported between the two arms, and the arm not taken is absent from the
taken branch's index. -/
noncomputable def runExitTwo
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .typeAVisibleEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (thetaFresh : K (data := data) .typeAExitTwoTheta ∉ known)
    (freeFresh : K (data := data) .typeAExitTwoFree ∉ known)
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    ExitTwoResult current known := by
  classical
  match typeAExitTwo history thetaFresh freeFresh with
  | .left realized =>
      exact .closed
        (closeIncompatible realized (K .selection) (K .typeAExitTwoTheta)
          (by simp [closureFresh]))
  | .right free => exact .free free

/-! ## What the two exits carry -/

theorem exitTwoClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitTwoClosedKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitTwoFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitTwoFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitTwoClosed_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitTwoClosedKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitTwoFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitTwoFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-! # The saturated exit chain, run: node `[99]`

Exit `(3)` of `def:typeA-saturated-exits`: *"a shared `P₁₃` window violates the
corresponding legal-label relation `C_s`"*.  The chain reaches it on node
`[97]`'s no arm, so the row is asked after a cursor carrying node `[93]`'s
visible-entry fact and the exit-`(1)`- and exit-`(2)`-free hypotheses; as at the
two earlier exits, the requirement is discharged by instance resolution against
the incoming index and the row names no producer and no execution position.

The yes arm is closed, and the closure is again not this block's assertion.
`lem:typeA-exits-discharged` says exit `(3)` is *"precisely failure of the legal
`P₁₃` label relation from `lem:labels`; by definition of the relation, it creates
a target event"*, and
`Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision` is that
construction: the collision's two attachment coordinates and its outside
connector close a simple cycle of the manuscript's own length `s + 2 + |i − j|`,
which the collision's own side condition declares accepted.  Node `[1]`'s
selection committed that the object carries no accepted cycle.  Neither fact
mentions the other, so Core's `closeIncompatible` appends the closure key from
the two committed statements.

The no arm carries the third clause of the manuscript's *"assume exits (1)--(3)
do not occur"*, which is the hypothesis the exit-`(4)` family of
`def:typeA-exit4-family` is built under at node `[101]`. -/

/-- **Node `[99]`, asked on node `[97]`'s free cursor.** -/
noncomputable def typeAExitThree
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .typeAVisibleEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (collisionFresh : K (data := data) .typeAExitThreeCollision ∉ known)
    (freeFresh : K (data := data) .typeAExitThreeFree ∉ known) :
    Decision (K (data := data) .typeAExitThreeCollision)
      (K (data := data) .typeAExitThreeFree) history :=
  typeAExitThreeDichotomy history (K .typeAVisibleEntry)
    (K .typeAExitThreeCollision) (K .typeAExitThreeFree) (fun fact => fact.down)
    (fun value => ⟨value⟩) (fun value => ⟨value⟩) collisionFresh freeFresh

/-! ## The closure of the yes arm -/

/-- **A `P₁₃` label collision at a shared window is impossible on this branch.**

Exit `(3)` says two outside vertices attach to one packed window, the simple
path joining them avoids that window, and the cycle their attachment coordinates
close through the window has accepted length -- which
`Graph.WindowLabelCollision.labelCollision_iff_not_safe` identifies with failure
of `lem:labels`' relation `C_s`.  The collision *builds* that cycle, and node
`[1]` selected an object with no accepted cycle.

The one thing the construction asks of the registered target is that the
degenerate closure be rejected, and that is `Data.degenerateClosureRejected`,
read from the presentation exactly as `Data.quadrilateralAccepted` is at node
`[68]`.  The contradiction is otherwise read off the two committed statements,
which is what makes the closure the framework's rather than a row's. -/
noncomputable instance typeAExitThreeCollisionClosed :
    Incompatible (Input BranchState Presentation presentation data)
      (K (data := data) .selection)
      (K (data := data) .typeAExitThreeCollision) where
  contradiction := fun _input selected exit => by
    obtain ⟨_packing, _valid, _maximal, _piece, _inside, _connected, _charge,
      _surplus, collision⟩ := exit.down
    exact selected.down.1
      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
        data.degenerateClosureRejected collision)

/-! ## The block, run -/

/-- The key index of node `[99]`'s closed arm: the label collision, closed
against the selection's own avoidance. -/
abbrev typeAExitThreeClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeAExitThreeCollision :: known

/-- The key index of node `[99]`'s no arm — the entry of node `[101]`. -/
abbrev typeAExitThreeFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitThreeFree :: known

/-- **The exits of node `[99]`.**

`closed` is the terminal `lem:typeA-exits-discharged` records for exit `(3)`;
`free` is the alternative the saturated exit list continues on at node
`[101]`. -/
inductive ExitThreeResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | closed
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitThreeClosedKeys known))
  | free
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (typeAExitThreeFreeKeys known))

/-- **Exit `(3)` of `def:typeA-saturated-exits`, run.**

The decision commits one arm; on the arm that carries the collision the closure
key is appended by `closeIncompatible` from node `[99]`'s fact and node `[1]`'s
selection, both read by exact key off the incoming index.  Nothing is
transported between the two arms, and the arm not taken is absent from the taken
branch's index. -/
noncomputable def runExitThree
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .typeAVisibleEntry) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (collisionFresh : K (data := data) .typeAExitThreeCollision ∉ known)
    (freeFresh : K (data := data) .typeAExitThreeFree ∉ known)
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    ExitThreeResult current known := by
  classical
  match typeAExitThree history collisionFresh freeFresh with
  | .left realized =>
      exact .closed
        (closeIncompatible realized (K .selection)
          (K .typeAExitThreeCollision) (by simp [closureFresh]))
  | .right free => exact .free free

/-! ## What the two exits carry -/

theorem exitThreeClosed_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeClosedKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitThreeFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitThreeClosed_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeClosedKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitThreeFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitThreeFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-! ## The chain so far: nodes `[95]`, `[97]`, `[99]`

The three rows compose on one immutable prefix: each exit's free arm is the
cursor the next exit is asked on, and every fact of the prefix -- the selection,
the return avoidance, node `[93]`'s port -- remains in the index each later row
receives. -/

/-- **The exits of the chain `[95]` → `[97]` → `[99]`.** -/
inductive ExitChainResult
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
  | free
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (K .typeASaturatedExitEntry ::
          typeAExitThreeFreeKeys
            (typeAExitTwoFreeKeys (typeAExitOneFreeKeys known))))

/-- **Exits `(1)`, `(2)` and `(3)`, run in the manuscript's order.**

Each later row's requirements are discharged against the previous exit's free
index, which still carries them: `def:typeA-saturated-exits` is a list walked on
one branch, not a set of independent questions. -/
noncomputable def runExitChain
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
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
    (closureFresh : closed (BranchState := BranchState)
      (presentation := presentation) (data := data) ∉ known) :
    ExitChainResult current known := by
  classical
  match runExitOne history returnFresh oneFreeFresh closureFresh with
  | .closed closedHistory => exact .exitOneClosed closedHistory
  | .free freeHistory =>
      match runExitTwo freeHistory (by simp [thetaFresh])
          (by simp [twoFreeFresh]) (by simp [closureFresh]) with
      | .closed closedHistory => exact .exitTwoClosed closedHistory
      | .free continuing =>
          match runExitThree continuing (by simp [collisionFresh])
              (by simp [threeFreeFresh]) (by simp [closureFresh]) with
          | .closed closedHistory => exact .exitThreeClosed closedHistory
          | .free surviving =>
              -- `lem:typeA-unpeeled-visible-routing` routes node `[99]`'s no
              -- arm into the shared exit segment, so its entry is committed
              -- here, refined out of node `[89]`'s saturation exactly as it is
              -- at node `[94]`.
              exact .free
                ((Spine.typeASaturatedExitEntryRow (K .typeASaturatedReceiver)
                    (K .typeASaturatedExitEntry) (by simp)
                    (fun _input fact => fact.down)
                    (fun _input value => ⟨value⟩)).run surviving
                  (by simp [entryFresh]))

end Hypostructure.Graph.Strategy.Spine

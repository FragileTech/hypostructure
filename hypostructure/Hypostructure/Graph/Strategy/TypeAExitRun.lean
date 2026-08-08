import Hypostructure.Graph.Strategy.SpineRows

/-!
# The saturated exit chain: node `[95]`

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
    obtain ⟨_packing, _valid, _maximal, _component, _present, _charge,
      _surplus, _receiver, _isReceiver, _saturated, package,
      return', accepted⟩ := exit.down
    exact Graph.VisibleEntry.not_shiftedCycleLength_of_returnLengthSets_disjoint
      data.LengthOK avoidance.down
      (Graph.VisibleEntry.mem_completionPorts.mp package.port).1 return' accepted

/-! ## Ledger indices -/

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

/-! # The saturated exit chain: node `[97]`

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
    obtain ⟨_packing, _valid, _maximal, _component, _present, _charge,
      _surplus, _receiver, _isReceiver, _saturated, package, pair⟩ := exit.down
    exact selected.down.1
      (Graph.VisibleEntry.hasCycleWithLength_of_exitTwoThrough package.port pair)

/-! ## Ledger indices -/

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

/-! # The saturated exit chain: node `[99]`

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
do not occur"*.  The canonical run stops at that exact fact until the shared
response-realization theorem needed by the exit-`(4)` family is available. -/

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
    obtain ⟨_packing, _valid, _maximal, _component, _present, _charge,
      _surplus, _receiver, _isReceiver, _saturated, _package, collision⟩ :=
      exit.down
    exact selected.down.1
      (Graph.WindowLabelCollision.hasCycleWithLength_of_labelCollision
        data.degenerateClosureRejected collision)

/-! ## Ledger indices -/

/-- The key index of node `[99]`'s closed arm: the label collision, closed
against the selection's own avoidance. -/
abbrev typeAExitThreeClosedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  closed :: K .typeAExitThreeCollision :: known

/-- The key index of node `[99]`'s no arm, retained as the current canonical
visible-branch boundary. -/
abbrev typeAExitThreeFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitThreeFree :: known

abbrev typeAExitFourKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFour :: known

abbrev typeAExitFourPeeledKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFourPeeled :: typeAExitFourKeys known

abbrev typeAExitFourLoopKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedExitEntry :: typeAExitFourPeeledKeys known

abbrev typeAExitFourFiniteDescentKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFourFiniteDescent :: known

abbrev typeASaturatedHandoffVisibleKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedHandoffVisible :: known

abbrev typeASaturatedHandoffSilentKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedHandoffSilent :: known

abbrev typeASaturatedHandoffExitFourKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedHandoffExitFour :: known

abbrev typeASaturatedHandoffExitFourFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeASaturatedHandoffExitFourFree :: known

abbrev typeAExitFiveKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFive :: known

abbrev typeAExitFiveFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFiveFree :: known

abbrev typeAExitSixKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSix :: known

abbrev typeAExitSixFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSixFree :: known

abbrev typeAExitSixProperKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSixProper :: typeAExitSixKeys known

abbrev typeAExitSixGlobalKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSixGlobal :: typeAExitSixKeys known

abbrev typeAExitSevenProducedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSevenProduced :: typeAExitSixFreeKeys known

abbrev typeAExitSevenHandoffKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSevenHandoff :: typeAExitSevenProducedKeys known

abbrev typeAExitSevenFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitSevenFree :: typeAExitSixFreeKeys known

abbrev route8ResidualKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .route8Residual :: typeAExitSevenFreeKeys known

abbrev typeAExitFourReceiverDischargedKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFourReceiverDischarged :: typeAExitFourPeeledKeys known

abbrev typeAExitFourFreeKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .typeAExitFourFree :: known

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

theorem exitFour_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFourFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFourPeeled_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourPeeledKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFourLoop_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourLoopKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFourFiniteDescent_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourFiniteDescentKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem saturatedHandoffVisible_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffVisibleKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem saturatedHandoffSilent_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffSilentKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem saturatedHandoffExitFour_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffExitFourKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem saturatedHandoffExitFourFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffExitFourFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFive_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFiveKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFiveFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFiveFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFourReceiverDischarged_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourReceiverDischargedKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitSix_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitSixFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitSixProper_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixProperKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitSixGlobal_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixGlobalKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitSevenProduced_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSevenProducedKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitSevenHandoff_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSevenHandoffKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitSevenFree_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSevenFreeKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem route8Residual_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (route8ResidualKeys known)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem exitFour_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitFourFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitFourPeeled_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourPeeledKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitFourLoop_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourLoopKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitFourFiniteDescent_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourFiniteDescentKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem saturatedHandoffVisible_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffVisibleKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem saturatedHandoffSilent_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffSilentKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem saturatedHandoffExitFour_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffExitFourKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem saturatedHandoffExitFourFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeASaturatedHandoffExitFourFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitFive_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFiveKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitFiveFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFiveFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitFourReceiverDischarged_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitFourReceiverDischargedKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitSix_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitSixFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitSixProper_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixProperKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitSixGlobal_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSixGlobalKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitSevenProduced_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSevenProducedKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitSevenHandoff_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSevenHandoffKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem exitSevenFree_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (typeAExitSevenFreeKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

theorem route8Residual_audit_facts_unique
    {selected : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (route8ResidualKeys known)) :
    (ExactLedger.audit history).facts.Nodup :=
  ExactLedger.audit_facts_unique history

/-! ## The chain so far: nodes `[95]`, `[97]`, `[99]`

The three rows compose on one immutable prefix: each exit's free arm is the
cursor the next exit is asked on, and every fact of the prefix -- the selection,
the return avoidance, node `[93]`'s port -- remains in the index each later row
receives. -/

end Hypostructure.Graph.Strategy.Spine

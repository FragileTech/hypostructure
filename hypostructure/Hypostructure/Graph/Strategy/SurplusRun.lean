import Hypostructure.Graph.Strategy.SurplusRows
import Hypostructure.Graph.Strategy.SpineRun

/-!
# The sparse surplus branch, run

Nodes `[126]`--`[128]`, on the arm node `[19]` sends an object whose degree
surplus exceeds the registered scale threshold.  The rows of `SurplusRows` are
each quantified over the keys they consume and produce; this module installs
them at the spine's own vocabulary and runs them in the manuscript's order
against the one canonical `ExactLedger`, over the literal ledger the entry
spine leaves at `Spine.Result.surplusAbove`.

Every prerequisite is discharged by instance resolution against the incoming
index: node `[127]` does not elaborate before node `[10]`'s slack-independence
entry, and node `[128]` does not elaborate before the node-`[1]`--`[4]`
selection entry.  Nothing is carried between rows but the residual and the
ledger, and no row names a producer or an execution position.

Node `[125]` is the *survivor* of the five sparse surplus exits of
`def:named-surplus-exits`.  Those exits are not yet branch alternatives of this
block -- exit `(e)` has no live support -- so this module runs the three rows
that do not depend on exit-freeness, and the arm it produces is the activation
data itself.  `lem:surviving-active-family`'s cardinality is committed;
its *"not removed by an exit"* clause and clause (b) of
`lem:sparse-port-activation` are not.
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
sparse-surplus key *is* the manuscript statement, so nothing is re-encoded. -/

/-- Node `[126]`: the sparse slack identity. -/
@[reducible] noncomputable def sparseSlackSurplus :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparseSlackSurplusRow (K .sparseSlackSurplus) (fun _input value => ⟨value⟩)

/-- Node `[127]`: the excess selector, its count, and the port structure. -/
@[reducible] noncomputable def activeSurplusFamily :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  activeSurplusFamilyRow (K .slackIndependent) (K .activeSurplusFamily)
    (by simp) (fun _input fact => fact.down) (fun _input value => ⟨value⟩)

/-- Node `[128]`: port activation.

The selection entry supplies both halves the suppression witness needs: the
object's own avoidance and its own minimality.  The minimality clause is read
at the registered progress, which is the canonical lexicographic one, so it is
exactly the raw hypothesis `TightVertexSuppression` asks for. -/
@[reducible] noncomputable def sparsePortActivation :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  sparsePortActivationRow (K .selection) (K .sparsePortActivation) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact smaller lexicographic baseline =>
      fact.down.2 smaller lexicographic baseline)
    (fun _input value => ⟨value⟩)

/-! ## The block, run -/

/-- The key index a branch carries after the three activation rows. -/
abbrev sparseActivationKeys
    (known : FactKeys (Input BranchState Presentation presentation data)) :
    FactKeys (Input BranchState Presentation presentation data) :=
  K .sparsePortActivation :: K .activeSurplusFamily :: K .sparseSlackSurplus ::
    known

/-- **The exit of the sparse activation block.**

There is one constructor: the block is nonbranching, and it carries the
canonical ledger indexed by exactly the three facts it appended. -/
inductive SurplusResult
    (selected : Input BranchState Presentation presentation data)
    (known : FactKeys (Input BranchState Presentation presentation data)) where
  | activated
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected (sparseActivationKeys known))

/-- **Nodes `[126]`--`[128]`, run.**

The three fact-only rows are composed by `AtomicCT.run`, which appends each
row's declared productions to the incoming index while retaining the literal
ancestry.  Every freshness side condition is decided on the vocabulary's own
finite `Key`. -/
noncomputable def runSparseActivation
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    [FactKeys.Has (K (data := data) .selection) known]
    [FactKeys.Has (K (data := data) .slackIndependent) known]
    (history : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (slackFresh : K (data := data) .sparseSlackSurplus ∉ known)
    (familyFresh : K (data := data) .activeSurplusFamily ∉ known)
    (activationFresh : K (data := data) .sparsePortActivation ∉ known) :
    SurplusResult current known := by
  classical
  have afterSlack :=
    (sparseSlackSurplus (data := data)).run history (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [slackFresh])
  have afterFamily :=
    (activeSurplusFamily (data := data)).run afterSlack (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [familyFresh])
  have afterActivation :=
    (sparsePortActivation (data := data)).run afterFamily (by
      intro key isNew isOld
      simp only [List.mem_singleton] at isNew
      subst isNew
      revert isOld
      simp [activationFresh])
  exact .activated afterActivation

/-- **The sparse surplus branch, entered from the entry spine's own exit.**

The predecessor is the literal ledger of `Spine.Result.surplusAbove`: node
`[19]`'s above arm, indexed by the nine facts that branch established.  Both
prerequisites -- the selection entry and node `[10]`'s slack independence -- are
in that index, so the block elaborates against it and nothing is re-selected or
re-proved. -/
noncomputable def runSurplusBranch
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (surplusAboveKeys (BranchState := BranchState)
        (presentation := presentation) (data := data))) :
    SurplusResult selected
      (surplusAboveKeys (BranchState := BranchState)
        (presentation := presentation) (data := data)) :=
  runSparseActivation history (by simp) (by simp) (by simp)

end Hypostructure.Graph.Strategy.Spine

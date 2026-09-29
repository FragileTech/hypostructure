import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdFirstFailure
import Hypostructure.Graph.Contracts.Spine.ColdMass

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- `[153]`'s returned residual and (★) cannot coexist
(`Contracts.Spine.not_distinct_of_coldRepeatedStateResidual`): a later row that
proves (★) on the residual arm closes it through Core's closure boundary. -/
noncomputable instance instIncompatibleColdRepeatedStateDistinct :
    Incompatible (Input BranchState Presentation presentation data)
      (K .coldRepeatedStateResidual) (K .coldCutStatesDistinct) where
  contradiction := fun _residual residual distinct =>
    Contracts.Spine.not_distinct_of_coldRepeatedStateResidual data.toParameters _
      residual.down distinct.down

/-- `[162]`'s returned residual and the heavy-entry test cannot coexist
(`Contracts.Spine.not_heavyEntryTerminal_of_residual`). -/
noncomputable instance instIncompatibleColdHeavyEntryTerminal :
    Incompatible (Input BranchState Presentation presentation data)
      (K .coldDenseHeavyEntryResidual) (K .coldHeavyEntryTerminal) where
  contradiction := fun _residual residual terminal =>
    Contracts.Spine.not_heavyEntryTerminal_of_residual data.toParameters _
      residual.down terminal.down

/-! ## Node `[153]`: the exact decision behind `lem:cold-corridor-first-failure` (ii)

At G the paper's (F2) (tex 7265-7270) is decided: it never fires.  What `[153]`
still splits is (★): G's pinned cut states along each retained cold corridor
are pairwise distinct up to the first failure, or some retained corridor of G
repeats a state first (an (F5) repeat with no earlier event).  The decision reads G's retained first-failure occurrence
(`K .coldFirstFailureOccurrence`) and splits (★) / ¬(★) at G.  On the (★) arm
routing continues; on the ¬(★) arm the explicitly constructed first equal-state
pair of G, with the profile separation of G's two readings and the equal capped
degrees of its glue vertices
(`Contracts.Spine.coldRepeatedStateResidual_of_not_distinct`), is published as
the returned residual `K .coldRepeatedStateResidual`.  (F2) is not what either
arm reads: it is decided at G on every corridor
(`Contracts.Spine.not_coldFirstFailureDefectAt`). -/
noncomputable def coldCutStatesDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    (distinctFresh : K .coldCutStatesDistinct ∉ known)
    (residualFresh : K .coldRepeatedStateResidual ∉ known) :
    Decision (K .coldCutStatesDistinct) (K .coldRepeatedStateResidual) previous := by
  classical
  -- The decision reads its predecessor fact at the one object it splits.
  have _occurrence := (previous.get (K .coldFirstFailureOccurrence)).down
  exact Decision.run previous (K .coldCutStatesDistinct) (K .coldRepeatedStateResidual)
    `Hypostructure.Graph.Strategy.Spine.coldCutStatesDichotomy
    (if distinct : ColdCutStatesDistinctStatement data.toParameters current.object then
      .inl ⟨distinct⟩
    else
      .inr ⟨Contracts.Spine.coldRepeatedStateResidual_of_not_distinct
        data.toParameters current.object distinct⟩)
    distinctFresh residualFresh

/-! ## Node `[162]`: the exact decision on the distinct-states arm

On the (★) arm the first failure of every retained corridor of G is read within
`Q_cold` states (`ColdEqualStates.first_lt_stateBound`) and is either the
terminal (F5) event or an (F4) heavy centre.  The only sub-case in which the
corridor can fail to be terminal is an (F4) heavy centre strictly before the
terminal segment on a corridor reading more than `Q_cold` states.  The
decision reads (★) (`K .coldCutStatesDistinct`) and splits that sub-case
exactly: every such corridor is terminal (`K .coldHeavyEntryTerminal`), or the
explicitly constructed long corridor through a heavy centre of G
(`Contracts.Spine.coldDenseHeavyEntryResidual_of_not_terminal`) is the
returned residual `K .coldDenseHeavyEntryResidual`. -/
noncomputable def coldHeavyEntryDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    (terminalFresh : K .coldHeavyEntryTerminal ∉ known)
    (residualFresh : K .coldDenseHeavyEntryResidual ∉ known) :
    Decision (K .coldHeavyEntryTerminal) (K .coldDenseHeavyEntryResidual) previous := by
  classical
  exact Decision.run previous (K .coldHeavyEntryTerminal) (K .coldDenseHeavyEntryResidual)
    `Hypostructure.Graph.Strategy.Spine.coldHeavyEntryDichotomy
    (if terminal : ColdHeavyEntryTerminalStatement data.toParameters current.object then
      .inl ⟨terminal⟩
    else
      .inr ⟨Contracts.Spine.coldDenseHeavyEntryResidual_of_not_terminal
        data.toParameters current.object
        (previous.get (K .coldCutStatesDistinct)).down terminal⟩)
    terminalFresh residualFresh

end Hypostructure.Graph.Strategy.Spine

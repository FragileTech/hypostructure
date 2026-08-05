import Hypostructure.Graph.Strategy.SpineRows

/-!
# The entry spine, composed

The rows of `SpineRows` are each quantified over the keys they consume and
produce.  This module installs them all at the spine's own vocabulary and runs
them in the manuscript's order against the one canonical ledger, from opening
the minimal-counterexample scope at node `[1]` to the density cap at node
`[24]`.

The result type is the statement being made.  `Result` has exactly three
constructors, because the spine has exactly three exits:

* the surplus split at node `[19]` sends a non-near-cubic object out of the
  block, with everything proved up to that point;
* the barrier comparison at node `[21]` sends an overflowing object out of the
  block, with everything proved up to that point;
* otherwise the block completes, and the ledger's key index is the full list of
  its ten facts.

A branch that left at `[19]` has no `[21]` fact in its index and vice versa, so
neither exit can read the other's alternative.  Nothing is carried between rows
but the residual and the ledger.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- The spine's own fact system, installed for the whole run.  It is the only
`FactSystem` on this residual domain, so every key below is one of its own. -/
noncomputable instance instFactSystem :
    FactSystem (Input BranchState Presentation presentation data) :=
  factSystem BranchState Presentation presentation data

/-- The spine's exact semantic keys. -/
abbrev K (k : Key) : FactKey (Input BranchState Presentation presentation data) :=
  FactVocabulary.WithClosure.fact k

/-- Distinct semantic keys are distinct exact keys.  Every freshness and
distinctness side condition below is discharged through this, so a disequality
is decided on the vocabulary's own finite `Key` and never on the residual
domain, which contains free parameters and cannot be evaluated. -/
@[simp] theorem key_inj {left right : Key} :
    (K left : FactKey (Input BranchState Presentation presentation data)) =
        K right ↔ left = right := by
  constructor
  · intro same; injection same
  · intro same; rw [same]

section Rows

variable (T : Core.Target (problem BranchState Presentation presentation data))
variable (targetPredicate :
  T.Predicate = Graph.HasCycleWithLength data.LengthOK)
variable (targetInvariant : Core.TargetInvariant
  (Graph.isomorphismEquivalenceWithPresentation
    (Graph.MinimumDegreeAtLeast data.threshold) BranchState
    Presentation presentation
    (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
  T.Predicate)

/-- Nodes `[5]`--`[7]`, at the spine's own keys. -/
@[reducible] noncomputable def returnAvoidance :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  returnAvoidanceRow (K .selection) (K .returnAvoidance) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[8]`. -/
@[reducible] noncomputable def noProperBaseline :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  noProperBaselineRow (K .selection) (K .noProperBaseline) (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down.2)
    (fun _input value => ⟨value⟩)

/-- Nodes `[9]`--`[10]`. -/
@[reducible] noncomputable def deletionCriticality :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  deletionCriticalityRow (K .noProperBaseline) (K .tightEndpoint)
    (K .slackIndependent) (by simp) (by simp) (by simp)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩) (fun _input value => ⟨value⟩)

/-- Nodes `[11]`--`[14]`. -/
@[reducible] noncomputable def interfaceReplacement :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  interfaceReplacementRow T targetInvariant (K .selection) (K .uncompressible)
    (by simp)
    (fun _input fact => by rw [targetPredicate]; exact fact.down.1)
    (fun _input fact smaller smallerLt baseline => by
      rw [targetPredicate]; exact fact.down.2 smaller smallerLt baseline)
    (fun _input value =>
      ⟨show ∀ support : Finset _input.object.Vertex,
          ¬ Graph.Strategy.InterfaceReplacement.CompressibleSupport
              (Graph.MinimumDegreeAtLeast data.threshold)
              (Graph.HasCycleWithLength data.LengthOK) _input.object support
        from targetPredicate ▸ value⟩)

/-- Nodes `[15]`--`[17]`. -/
@[reducible] noncomputable def obstructionPacking :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  obstructionPackingRow (K .selection) (K .maximalPacking) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Node `[18]`. -/
@[reducible] noncomputable def localAlgebra :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  localAlgebraRow (K .maximalPacking) (K .localAlgebra) (by simp)
    (fun _input value => ⟨value⟩)

/-- Nodes `[25]`--`[27]`. -/
@[reducible] noncomputable def remainderNormalization :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  remainderNormalizationRow (K .selection) (K .remainderNormalized) (by simp)
    (fun _input fact => fact.down.1) (fun _input value => ⟨value⟩)

/-- Nodes `[22]`--`[24]`. -/
@[reducible] noncomputable def densityBudget :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  densityBudgetRow (K .barrierCap) (K .surplusAtOrBelow) (K .densityCap)
    (by simp)
    (fun _input fact => fact.down.1)
    (fun _input fact => fact.down)
    (fun _input value => ⟨value⟩)

/-- Nodes `[28]`--`[29]`. -/
@[reducible] noncomputable def boundaryDemand :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  boundaryDemandRow (K .remainderNormalized) (K .boundaryDemand) (by simp)
    (fun _input value => ⟨value⟩)

end Rows

/-- The key index of a ledger that has completed the block. -/
abbrev completedKeys : FactKeys (Input BranchState Presentation presentation data) :=
  [K .boundaryDemand, K .remainderNormalized, K .densityCap, K .barrierCap, K .surplusAtOrBelow, K .localAlgebra,
    K .maximalPacking, K .uncompressible, K .tightEndpoint,
    K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
    K .selection]

/-- The key index of a ledger that left the block at node `[19]`. -/
abbrev surplusAboveKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .surplusAbove, K .localAlgebra, K .maximalPacking, K .uncompressible,
    K .tightEndpoint, K .slackIndependent, K .noProperBaseline,
    K .returnAvoidance, K .selection]

/-- The key index of a ledger that left the block at node `[21]`. -/
abbrev barrierOverflowKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .barrierOverflow, K .surplusAtOrBelow, K .localAlgebra,
    K .maximalPacking, K .uncompressible, K .tightEndpoint,
    K .slackIndependent, K .noProperBaseline, K .returnAvoidance,
    K .selection]

/-- **The three exits of the entry spine.**

Each constructor carries the canonical ledger at the residual the block was
argued about, indexed by exactly the facts that branch established.  There is
no fourth constructor and no payload beside the ledger. -/
inductive Result (selected : Input BranchState Presentation presentation data)
    where
  | surplusAbove
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected surplusAboveKeys)
  | barrierOverflow
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected barrierOverflowKeys)
  | complete
      (history : ExactLedger (Input BranchState Presentation presentation data)
        selected completedKeys)

/-- **Block A, run.**

The fact-only rows are composed by `AtomicCT.run`, which appends each row's
declared productions to the incoming index; the two diamonds are composed by
`Decision.run`, which commits the arm actually taken and leaves the other
arm's key out of this branch's index entirely.

Every prerequisite is discharged by instance resolution against the incoming
index -- a row that asked for a fact the branch has not proved would not
elaborate -- and every freshness side condition is decided on the exact keys.
No row names a producer, a predecessor, or an execution position. -/
noncomputable def run
    (T : Core.Target (problem BranchState Presentation presentation data))
    (targetPredicate : T.Predicate = Graph.HasCycleWithLength data.LengthOK)
    (targetInvariant : Core.TargetInvariant
      (Graph.isomorphismEquivalenceWithPresentation
        (Graph.MinimumDegreeAtLeast data.threshold) BranchState
        Presentation presentation
        (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
      T.Predicate)
    (opened : OpenedScope
      (P := problem BranchState Presentation presentation data) (K .selection)) :
    Result opened.selected := by
  classical
  -- Nodes `[5]`--`[18]`: seven fact-only rows against one immutable prefix.
  have afterReturn :=
    (returnAvoidance (data := data)).run opened.history (by simp)
  have afterProper :=
    (noProperBaseline (data := data)).run afterReturn (by simp)
  have afterCriticality :=
    (deletionCriticality (data := data)).run afterProper (by simp)
  have afterReplacement :=
    (interfaceReplacement T targetPredicate targetInvariant).run
      afterCriticality (by simp)
  have afterPacking :=
    (obstructionPacking (data := data)).run afterReplacement (by simp)
  have afterAlgebra := (localAlgebra (data := data)).run afterPacking (by simp)
  -- Node `[19]`: the surplus split.
  match surplusDichotomy afterAlgebra (K .surplusAbove) (K .surplusAtOrBelow)
      (fun above => ⟨above⟩) (fun atOrBelow => ⟨atOrBelow⟩)
      (by simp) (by simp) with
  | .left aboveHistory => exact .surplusAbove aboveHistory
  | .right belowHistory =>
      -- Node `[21]`: the finite barrier enumeration.
      match barrierEnumerationDichotomy belowHistory (K .barrierCap)
          (K .barrierOverflow) (fun cap => ⟨cap⟩) (fun overflow => ⟨overflow⟩)
          (by simp) (by simp) with
      | .right overflowHistory => exact .barrierOverflow overflowHistory
      | .left capHistory =>
          -- Nodes `[22]`--`[24]`: spend the retained cap.
          -- Nodes `[25]`--`[27]`: normalize the packed-window remainder.
          -- Nodes `[25]`--`[29]`: normalize the remainder, then account for
          -- its boundary demand.
          exact .complete
            ((boundaryDemand (data := data)).run
              ((remainderNormalization (data := data)).run
                ((densityBudget (data := data)).run capHistory (by simp))
                (by simp))
              (by simp))

/-! ## What the run leaves behind -/

/-- **The audit of a completed block is exactly its ten facts, in the order
they were committed.**

The audit reads the ledger's own key index, so this is the statement that the
block committed these ten and nothing else -- no closure entry, no bookkeeping
fact, no duplicate. -/
theorem complete_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected completedKeys) :
    (ExactLedger.audit history).facts =
      [`Hypostructure.Graph.Strategy.Spine.boundaryDemand,
        `Hypostructure.Graph.Strategy.Spine.remainderNormalized,
        `Hypostructure.Graph.Strategy.Spine.densityCap,
        `Hypostructure.Graph.Strategy.Spine.barrierCap,
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow,
        `Hypostructure.Graph.Strategy.Spine.localAlgebra,
        `Hypostructure.Graph.Strategy.Spine.maximalPacking,
        `Hypostructure.Graph.Strategy.Spine.uncompressible,
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint,
        `Hypostructure.Graph.Strategy.Spine.slackIndependent,
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline,
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance,
        `Hypostructure.Graph.Strategy.Spine.selection] := rfl

/-- **Every fact of a completed block is accounted for by a chronological
commit.**  Nothing was archived, rebased, or dropped along the way. -/
theorem complete_audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected completedKeys) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

/-- **The two exits carry strictly less.**  A branch that left at node `[19]`
never records the near-cubic arm, and a branch that left at node `[21]` never
records the cap -- each exit's audit is its own prefix of the block. -/
theorem surplusAbove_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected surplusAboveKeys) :
    (ExactLedger.audit history).facts =
      [`Hypostructure.Graph.Strategy.Spine.surplusAbove,
        `Hypostructure.Graph.Strategy.Spine.localAlgebra,
        `Hypostructure.Graph.Strategy.Spine.maximalPacking,
        `Hypostructure.Graph.Strategy.Spine.uncompressible,
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint,
        `Hypostructure.Graph.Strategy.Spine.slackIndependent,
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline,
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance,
        `Hypostructure.Graph.Strategy.Spine.selection] := rfl

theorem barrierOverflow_audit_facts
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected barrierOverflowKeys) :
    (ExactLedger.audit history).facts =
      [`Hypostructure.Graph.Strategy.Spine.barrierOverflow,
        `Hypostructure.Graph.Strategy.Spine.surplusAtOrBelow,
        `Hypostructure.Graph.Strategy.Spine.localAlgebra,
        `Hypostructure.Graph.Strategy.Spine.maximalPacking,
        `Hypostructure.Graph.Strategy.Spine.uncompressible,
        `Hypostructure.Graph.Strategy.Spine.tightEndpoint,
        `Hypostructure.Graph.Strategy.Spine.slackIndependent,
        `Hypostructure.Graph.Strategy.Spine.noProperBaseline,
        `Hypostructure.Graph.Strategy.Spine.returnAvoidance,
        `Hypostructure.Graph.Strategy.Spine.selection] := rfl

end Hypostructure.Graph.Strategy.Spine

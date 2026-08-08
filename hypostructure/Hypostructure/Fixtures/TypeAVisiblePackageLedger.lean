import Hypostructure.Graph.Strategy.SpineRows

/-!
# Fixture: selected Type A visible-package ledger refinement

The fixture runs the visible-package response/germ prefix directly on the
canonical one-fact ledger.  The row reads the exact package selected at node
`[93]`, commits one semantic fact, and retains that incoming fact literally.
It does not assert Q1 response classification or construct a separation.
-/

namespace Hypostructure.Fixtures.TypeAVisiblePackageLedger

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

noncomputable section

local instance : FactSystem
    (Input BranchState Presentation presentation data) :=
  factSystem BranchState Presentation presentation data

noncomputable abbrev K (keyName : Key) :
    FactKey (Input BranchState Presentation presentation data) :=
  key BranchState Presentation presentation data keyName

abbrev incomingKeys :
    FactKeys (Input BranchState Presentation presentation data) :=
  [K .typeAVisibleEntry]

theorem incomingKeys_nodup :
    (incomingKeys (BranchState := BranchState) (presentation := presentation)
      (data := data)).Nodup := by
  change [
    (FactVocabulary.WithClosure.fact Key.typeAVisibleEntry :
      (vocabulary BranchState Presentation presentation data).WithClosure)].Nodup
  simp

theorem output_fresh :
    List.Disjoint
      [K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleEntryClause]
      (incomingKeys (BranchState := BranchState) (presentation := presentation)
        (data := data)) := by
  change List.Disjoint
    [(FactVocabulary.WithClosure.fact Key.typeAVisibleEntryClause :
      (vocabulary BranchState Presentation presentation data).WithClosure)]
    [(FactVocabulary.WithClosure.fact Key.typeAVisibleEntry :
      (vocabulary BranchState Presentation presentation data).WithClosure)]
  simp

noncomputable abbrev row :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  typeAVisibleEntryClauseRow
    (BranchState := BranchState) (Presentation := Presentation)
    (presentation := presentation) (data := data)
    (K .typeAVisibleEntry) (K .typeAVisibleEntryClause) (by simp)
    (fun _input fact => fact.down)
    (fun _input payload => ⟨payload⟩)

example :
    (row (BranchState := BranchState) (presentation := presentation)
      (data := data)).manifest.Requires = incomingKeys :=
  rfl

example :
    (row (BranchState := BranchState) (presentation := presentation)
      (data := data)).manifest.Produces = [K .typeAVisibleEntryClause] :=
  rfl

noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected incomingKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      (K .typeAVisibleEntryClause :: incomingKeys) :=
  (row (BranchState := BranchState) (presentation := presentation)
    (data := data)).run history output_fresh

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeAVisibleEntry) ∈
      (K (BranchState := BranchState) (presentation := presentation)
          (data := data) .typeAVisibleEntryClause ::
        incomingKeys (BranchState := BranchState) (presentation := presentation)
          (data := data)) := by
  simp [incomingKeys]

theorem audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeAVisibleEntryClause :: incomingKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem every_commit_is_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeAVisibleEntryClause :: incomingKeys)) :
    (ExactLedger.audit history).commits.Forall
      (fun record => record.produced ≠ []) :=
  ExactLedger.audit_commits_nonempty history

end

end Hypostructure.Fixtures.TypeAVisiblePackageLedger

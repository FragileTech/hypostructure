import Hypostructure.Graph.Strategy.SpineRows

/-!
# Fixture: the immediate B2(a)--(c) disjoint-ledger handoff

This fixture instantiates the generic fact-only row directly on the spine's
closed vocabulary.  Its incoming index contains exactly the three facts the
executor reads; its output index retains all three and prepends the one
disjoint-ledger fact.  No assembly topology or B2(d) datum is involved.
-/

namespace Hypostructure.Fixtures.TypeBDisjointLedgerHandoff

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
  [K .typeBB2Choice, K .selection, K .remainderNormalized]

theorem incomingKeys_nodup :
    (incomingKeys (BranchState := BranchState) (presentation := presentation)
      (data := data)).Nodup := by
  change [
    (FactVocabulary.WithClosure.fact Key.typeBB2Choice :
      (vocabulary BranchState Presentation presentation data).WithClosure),
    (FactVocabulary.WithClosure.fact Key.selection :
      (vocabulary BranchState Presentation presentation data).WithClosure),
    (FactVocabulary.WithClosure.fact Key.remainderNormalized :
      (vocabulary BranchState Presentation presentation data).WithClosure)].Nodup
  simp

theorem output_fresh :
    List.Disjoint
      [K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBDisjointLedger]
      (incomingKeys (BranchState := BranchState) (presentation := presentation)
        (data := data)) := by
  change List.Disjoint
    [(FactVocabulary.WithClosure.fact Key.typeBDisjointLedger :
      (vocabulary BranchState Presentation presentation data).WithClosure)]
    [(FactVocabulary.WithClosure.fact Key.typeBB2Choice :
      (vocabulary BranchState Presentation presentation data).WithClosure),
      (FactVocabulary.WithClosure.fact Key.selection :
        (vocabulary BranchState Presentation presentation data).WithClosure),
      (FactVocabulary.WithClosure.fact Key.remainderNormalized :
        (vocabulary BranchState Presentation presentation data).WithClosure)]
  simp

example :
    (typeBDisjointLedgerRow (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation) (data := data)
      (K .typeBB2Choice) (K .selection)
      (K .remainderNormalized) (K .typeBDisjointLedger) incomingKeys_nodup
      (fun _input fact => fact.down) (fun _input fact => fact.down.1)
      (fun _input fact => fact.down) (fun _input handoff => ⟨handoff⟩)).manifest.Requires =
        incomingKeys :=
  rfl

example :
    (typeBDisjointLedgerRow (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation) (data := data)
      (K .typeBB2Choice) (K .selection)
      (K .remainderNormalized) (K .typeBDisjointLedger) incomingKeys_nodup
      (fun _input fact => fact.down) (fun _input fact => fact.down.1)
      (fun _input fact => fact.down) (fun _input handoff => ⟨handoff⟩)).manifest.Produces =
        [K .typeBDisjointLedger] :=
  rfl

noncomputable def run
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected incomingKeys) :
    ExactLedger (Input BranchState Presentation presentation data) selected
      (K .typeBDisjointLedger :: incomingKeys) :=
  (typeBDisjointLedgerRow (BranchState := BranchState)
    (Presentation := Presentation) (presentation := presentation) (data := data)
    (K .typeBB2Choice) (K .selection)
    (K .remainderNormalized) (K .typeBDisjointLedger) incomingKeys_nodup
    (fun _input fact => fact.down) (fun _input fact => fact.down.1)
    (fun _input fact => fact.down) (fun _input handoff => ⟨handoff⟩)).run history
      output_fresh

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .typeBB2Choice) ∈
      (K (BranchState := BranchState) (presentation := presentation) (data := data)
          .typeBDisjointLedger ::
        incomingKeys (BranchState := BranchState) (presentation := presentation)
          (data := data)) := by
  simp [incomingKeys]

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .selection) ∈
      (K (BranchState := BranchState) (presentation := presentation) (data := data)
          .typeBDisjointLedger ::
        incomingKeys (BranchState := BranchState) (presentation := presentation)
          (data := data)) := by
  simp [incomingKeys]

example :
    (K (BranchState := BranchState) (presentation := presentation) (data := data)
        .remainderNormalized) ∈
      (K (BranchState := BranchState) (presentation := presentation) (data := data)
          .typeBDisjointLedger ::
        incomingKeys (BranchState := BranchState) (presentation := presentation)
          (data := data)) := by
  simp [incomingKeys]

/-- The committed fact exposes the one retained ledger and the universal
post-ledger component proposition, rather than one commit per component. -/
theorem committed_components
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeBDisjointLedger :: incomingKeys)) :
    ∃ packing : Finset (Finset selected.object.Vertex),
      selected.object.IsWindowPacking data.windowOrder packing ∧
        (∀ window : Finset selected.object.Vertex,
          selected.object.InducesWindow data.windowOrder window →
          ∃ member ∈ packing, ¬ Disjoint window member) ∧
        ∃ canonicalPiece :
            Graph.TypeBRefinedSupport.CanonicalPiece selected.object packing,
          selected.object.NegativeNetCharge canonicalPiece.vertices data.threshold
              data.dischargeScale ∧
            0 < selected.object.ambientSurplus canonicalPiece.vertices
              data.threshold ∧
            ∃ ledger : Graph.TypeBRefinedSupport.DisjointLedger selected.object
                data.threshold data.dischargeScale canonicalPiece,
              ledger.ExactAugmentedLedgerRefinement ∧
                ∀ component : Graph.SupportComponents.Connected.Component
                    selected.object ledger.remainingCore,
                  component ∈ Graph.SupportComponents.Connected.order
                      selected.object ledger.remainingCore →
                    Graph.TypeBPostLedgerCore.PostLedgerComponent
                      data.typeABPresentation ledger component :=
  (ExactLedger.get history (K .typeBDisjointLedger)).down

theorem audit_accounts_for_every_fact
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeBDisjointLedger :: incomingKeys)) :
    (ExactLedger.audit history).facts =
      (ExactLedger.audit history).commits.reverse.flatMap
        (fun record => record.produced) :=
  ExactLedger.audit_complete history

theorem every_commit_is_nonempty
    {selected : Input BranchState Presentation presentation data}
    (history : ExactLedger (Input BranchState Presentation presentation data)
      selected (K .typeBDisjointLedger :: incomingKeys)) :
    (ExactLedger.audit history).commits.Forall
      (fun record => record.produced ≠ []) :=
  ExactLedger.audit_commits_nonempty history

end

end Hypostructure.Fixtures.TypeBDisjointLedgerHandoff

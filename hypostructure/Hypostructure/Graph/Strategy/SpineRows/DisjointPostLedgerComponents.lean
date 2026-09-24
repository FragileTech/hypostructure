import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## B2 and the live Type B post-ledger core

The successful finite choice above is turned into the manuscript's literal
augmented-ledger partition.  Remainder normalization supplies both window
freeness and the empty internal baseline core; the latter implies hereditary
Type A uncompressibility.  Selection supplies contextual target safety.  Every
remaining connected component is therefore passed to the existing Type A
hygiene theorem on the same ledger, and the component fact reads the ledger's
own `noHighCentre_remaining` theorem for the Type B maximal-core clause.  The
same fact also reads the branch's `uncompressible` entry and packages actual
component-indexed exit-`(7)` productions into the canonical grouped decorated
envelope. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def disjointPostLedgerComponentsRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
      (instFactSystem (BranchState := BranchState)
        (Presentation := Presentation) (presentation := presentation)
        (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.disjointPostLedgerComponents
    { Requires := [K .typeBB2Choice, K .selection, K .uncompressible,
        K .remainderNormalized]
      Produces := [K .typeBDisjointLedger]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let choiceFact := (inputs.get (K .typeBB2Choice)).down
      let avoids := (inputs.get (K .selection)).down.1
      let uncompressibleFact := (inputs.get (K .uncompressible)).down
      let normalized := (inputs.get (K .remainderNormalized)).down
      .cons (key := K .typeBDisjointLedger)
        (⟨by
          classical
          obtain ⟨packing, valid, maximal, canonicalPiece, centres, assigned,
            choice⟩ := choiceFact
          let ledger : Graph.TypeBRefinedSupport.DisjointLedger
              inputs.current.object data.threshold data.dischargeScale
                packing canonicalPiece.vertices centres :=
            ⟨Classical.choice choice,
              TypeBAssignedCentres.high data inputs.current.object assigned,
              TypeBAssignedCentres.centres_subset data inputs.current.object assigned⟩
          have noBaselineSubsupport : ∀ support : Finset inputs.current.object.Vertex,
              support ⊆ inputs.current.object.remainderSupport packing →
                ¬ Graph.MinimumDegreeAtLeast data.threshold
                  (inputs.current.object.induce support) := by
            intro support subset
            exact (normalized packing valid maximal support subset).2
          have pieceFree : Graph.InducedPathFree
              (inputs.current.object.induce canonicalPiece.vertices)
              data.windowOrder :=
            Graph.FiniteObject.inducedPathFree_induce_of_forall
              inputs.current.object
              (fun support subset =>
                (normalized packing valid maximal support
                  (subset.trans canonicalPiece.vertices_subset_remainder)).1)
          have emptyInternal : Graph.TypeAB.EmptyInternalThreeCore
              data.typeABPresentation inputs.current.object
                canonicalPiece.vertices :=
            Graph.TypeBPostLedgerCore.emptyInternalThreeCore_of_noBaselineSubsupport
              (threshold := data.threshold) rfl
              (fun support subset =>
                noBaselineSubsupport support
                  (subset.trans canonicalPiece.vertices_subset_remainder))
          have targetSafe : Graph.TypeAB.ContextuallyDyadicSafe
              data.typeABPresentation inputs.current.object := by
            simpa [Graph.TypeAB.ContextuallyDyadicSafe,
              Data.typeABPresentation] using avoids
          have hereditary : Graph.TypeAB.HereditarilyTargetUncompressible
              data.typeABPresentation inputs.current.object
                canonicalPiece.vertices :=
            Graph.TypeAB.hereditarilyTargetUncompressible_of_emptyInternalThreeCore
              emptyInternal
          have baseline : ∀ vertex : inputs.current.object.Vertex,
              data.threshold ≤ inputs.current.object.degree vertex := fun vertex =>
            le_trans inputs.current.baseline
              (inputs.current.object.minDegree_le_degree vertex)
          let componentFacts :
              ∀ component : Graph.SupportComponents.Connected.Component
                  inputs.current.object ledger.remainingCore,
                component ∈ Graph.SupportComponents.Connected.order
                    inputs.current.object ledger.remainingCore →
                  Graph.TypeBPostLedgerCore.PostLedgerComponent
                    data.typeABPresentation ledger component :=
            fun component componentMember =>
              Graph.TypeBPostLedgerCore.postLedgerCoreHygiene
                data.typeABPresentation ledger component componentMember rfl
                noBaselineSubsupport pieceFree targetSafe hereditary baseline
          have groupedCoverage :
              ∀ components :
                  Finset (Graph.TypeBMaximalCompletion.RemainingComponent
                    ledger),
                (∀ component ∈ components,
                  component ∈ Graph.SupportComponents.Connected.order
                    inputs.current.object ledger.remainingCore) →
                  ∀ production : ∀ component :
                      Graph.TypeBMaximalCompletion.SelectedComponent ledger
                        components,
                    Graph.TypeBMaximalCompletion.ComponentExitSeven ledger
                      component.1 data.LengthOK
                      (handoffHighDegree data inputs.current.object)
                      (handoffAbsorbing data inputs.current.object packing),
                    ∃ grouped :
                      Graph.DecoratedHandoff.GroupedEnvelopes
                        inputs.current.object data.LengthOK
                        (handoffUncompressible data inputs.current.object)
                        (handoffWindowFree data inputs.current.object)
                        (handoffHighDegree data inputs.current.object)
                        (handoffAbsorbing data inputs.current.object packing)
                        (Graph.TypeBMaximalCompletion.SelectedComponent ledger
                          components),
                      (∀ component :
                          Graph.TypeBMaximalCompletion.SelectedComponent ledger
                            components,
                        (grouped.envelope component).core =
                          Graph.SupportComponents.Connected.vertices
                            inputs.current.object ledger.remainingCore
                            component.1) ∧
                        ∀ centre : inputs.current.object.Vertex,
                          centre ∈ grouped.centres ↔
                            ∃ component :
                              Graph.TypeBMaximalCompletion.SelectedComponent
                                ledger components,
                              centre =
                                (production component).separation.separator := by
            intro components componentsSubset production
            have windowFree : ∀ component, component ∈ components →
                handoffWindowFree data inputs.current.object
                  (Graph.SupportComponents.Connected.vertices
                    inputs.current.object ledger.remainingCore component) := by
              intro component componentMember
              have orderMember := componentsSubset component componentMember
              have componentData := componentFacts component orderMember
              constructor
              · intro window windowSubset induces
                exact (normalized packing valid maximal window
                  (windowSubset.trans componentData.containedInRemainder)).1
                  induces
              · intro internal internalSubset
                exact (normalized packing valid maximal internal
                  (internalSubset.trans componentData.containedInRemainder)).2
            let grouped :=
              Graph.TypeBMaximalCompletion.groupedOfComponentExitSeven
                ledger components production avoids windowFree
                uncompressibleFact
            refine ⟨grouped, ?_, ?_⟩
            · intro component
              exact Graph.TypeBMaximalCompletion.Grouped.envelope_core
                ledger components production avoids windowFree
                uncompressibleFact component
            · intro centre
              exact Graph.TypeBMaximalCompletion.Grouped.mem_centres_iff
                ledger components production avoids windowFree
                uncompressibleFact centre
          exact Or.inl ⟨packing, valid, maximal, canonicalPiece, centres,
            assigned, ledger, ledger.exactAugmentedLedgerRefinement,
            componentFacts, groupedCoverage⟩
          rename_i remaining
          rcases remaining with absorbed | sameToken
          · refine Or.inr (Or.inl ⟨absorbed, ?_⟩)
            intro germ centre witness
            obtain ⟨choice⟩ := absorbed.2 germ centre witness
            refine ⟨choice, ?_⟩
            intro member
            exact (Graph.TypeBRefinedSupport.mem_candidateFamily_iff.mp
              (choice.eligible centre member)).2.entryRefines
          · obtain ⟨packing, valid, maximal, core, envelope, coreEq, nonempty,
                marked, directFree, choice⟩ := sameToken
            obtain ⟨selected⟩ := choice
            exact Or.inr (Or.inr ⟨packing, valid, maximal, core, envelope,
              coreEq, nonempty, marked, directFree, selected,
              fun centre member =>
                (Graph.TypeBRefinedSupport.mem_candidateFamily_iff.mp
                  (selected.eligible centre member)).2.entryRefines⟩)
        ⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine

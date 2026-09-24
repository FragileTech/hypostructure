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

/-! ## `prop:typeB-bridge-reduction` at every negative positive-surplus piece

The contrapositive `thm:branch-kill`(b) carries, produced once for the whole
remainder: at each negative positive-surplus canonical piece, the finite B2
alternative `b2_or_overlap` at the piece's own high centres either yields the
disjoint choice — whose ledger's exact augmented refinement would force
`N₀ ≥ 0` if the remaining scaled core charge were nonnegative
(`nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg`), so the
negative piece records the strictly negative core with every remaining
component passed through `lem:typeB-postledger-core-hygiene` and the B2(d)
grouped decorated envelope coverage — or a minimal Type B overlap obstruction
(`lem:typeB-bridge-to-overlap`).  Remainder normalization supplies window
freeness and the empty internal baseline core, selection supplies contextual
target safety, and the committed uncompressibility feeds the grouped envelope
step, exactly as in the selected-support B2 row above. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def typeBBridgeReductionRow :
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
    `Hypostructure.Graph.Strategy.Spine.typeBBridgeReduction
    { Requires := [K .selection, K .uncompressible, K .remainderNormalized]
      Produces := [K .typeBBridgeReduction]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let avoids := (inputs.get (K .selection)).down.1
      let uncompressibleFact := (inputs.get (K .uncompressible)).down
      let normalized := (inputs.get (K .remainderNormalized)).down
      .cons (key := K .typeBBridgeReduction)
        (⟨by
          classical
          intro packing valid maximal canonicalPiece negative _surplusPos
          rcases Graph.TypeBRefinedSupport.b2_or_overlap inputs.current.object
              data.threshold data.dischargeScale packing canonicalPiece.vertices
              (Graph.TypeBRefinedSupport.centres inputs.current.object
                data.threshold canonicalPiece.vertices)
              (Graph.TypeBRefinedSupport.centres_high inputs.current.object
                data.threshold canonicalPiece.vertices) with
            choice | obstruction
          · -- B2 disjoint choice: assemble the ledger at the piece's own
            -- high centres.
            let ledger : Graph.TypeBRefinedSupport.DisjointLedger
                inputs.current.object data.threshold data.dischargeScale
                  packing canonicalPiece.vertices
                  (Graph.TypeBRefinedSupport.centres inputs.current.object
                    data.threshold canonicalPiece.vertices) :=
              ⟨Classical.choice choice,
                Graph.TypeBRefinedSupport.centres_high inputs.current.object
                  data.threshold canonicalPiece.vertices,
                Finset.Subset.refl _⟩
            have noBaselineSubsupport :
                ∀ support : Finset inputs.current.object.Vertex,
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
                data.threshold ≤ inputs.current.object.degree vertex :=
              fun vertex =>
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
                            Graph.TypeBMaximalCompletion.SelectedComponent
                              ledger components,
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
            have notClean : ¬ (0 : Int) ≤ ∑ vertex ∈ ledger.remainingCore,
                Graph.TypeBRefinedSupport.scaledCoreCharge inputs.current.object
                  data.threshold data.dischargeScale canonicalPiece.vertices
                  vertex := by
              intro clean
              have nonnegative :=
                Graph.TypeBEnvelopeCharge.nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg
                  (object := inputs.current.object) ledger
                  ledger.exactAugmentedLedgerRefinement clean
              exact (inputs.current.object.not_negativeNetCharge_iff
                canonicalPiece.vertices data.threshold
                  data.dischargeScale).mpr nonnegative negative
            exact Or.inl ⟨ledger, ledger.exactAugmentedLedgerRefinement,
              notClean, componentFacts, groupedCoverage⟩
          · exact Or.inr obstruction⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine

import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePressureLedger
import Hypostructure.Graph.GluedCrossingCycle
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[178]` / open node `[182]`: decide the manuscript's conditional
factorization assertion on the one exact pair-response system already stored
in the ledger.  The positive arm is the sole input of
`lem:pair-failure-overlap`; the negative arm retains that same system as the
uncovered residual and asserts no blocker, exit, quotient, or contradiction. -/
noncomputable def pairConditionalFactorizationDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .pairOverlapSystem) known]
    (factorizationFresh : K .pairConditionalFactorization ∉ known)
    (residualFresh : K .pairConditionalFactorizationResidual ∉ known) :
    Decision (K .pairConditionalFactorization)
      (K .pairConditionalFactorizationResidual) previous := by
  classical
  let system := Classical.choice
    (previous.get (K .pairOverlapSystem)).down
  exact Decision.run previous (K .pairConditionalFactorization)
    (K .pairConditionalFactorizationResidual)
    `Hypostructure.Graph.Strategy.Spine.pairConditionalFactorizationDichotomy
    (if factorization : system.ConditionalFactorization then
      .inl ⟨⟨system, factorization⟩⟩
    else
      .inr ⟨⟨.factorization system factorization⟩⟩)
    factorizationFresh residualFresh

/-- **`lem:pair-failure-overlap` at node `[178]`.**

The row reads the exact failed response system together with the affirmative
conditional-factorization fact from the ledger.  It proves only the paper's
inclusion-minimal overlap conclusion.  A nonfactorizing system cannot enter
this row; it remains at node `[182]`. -/
@[reducible] noncomputable def pairFailureOverlapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairFailureOverlap
    { Requires := [K .pairConditionalFactorization]
      Produces := [K .pairFailureOverlap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      -- The minimal overlap is selected over the abstract current object.
      let overlap : PairFailureOverlap data.toParameters inputs.current.object :=
        (fun (object : Graph.FiniteObject.{u})
            (factorizationHolds : Holds BranchState Presentation presentation
              data .pairConditionalFactorization object) =>
          (show PairFailureOverlap data.toParameters object from by
            classical
            let factorizationFact := Classical.choice factorizationHolds
            let system := factorizationFact.1
            have factorization : system.ConditionalFactorization :=
              factorizationFact.2
            let candidates := system.failedFamily.powerset.filter system.obstruction
            have candidatesNonempty : candidates.Nonempty := by
              refine ⟨system.failedFamily, ?_⟩
              simp [candidates, PairOverlapSystem.obstruction,
                PairOverlapSystem.realizingOrder,
                PairOverlapSystem.toSkeletonModel,
                system.failedFamily_nonempty, system.failedFamily_obstruction]
            let selected := candidates.exists_minimal candidatesNonempty
            let family := Classical.choose selected
            have selectedFacts : family ∈ candidates ∧
                ∀ candidate ∈ candidates, candidate ⊆ family →
                  family ⊆ candidate := by
              exact Classical.choose_spec selected
            have familyFacts : family ⊆ system.failedFamily ∧
                system.obstruction family := by
              simpa [candidates] using selectedFacts.1
            have minimal : system.minimalObstruction family := by
              refine ⟨familyFacts.2, ?_⟩
              intro proper properSubset properNonempty
              by_contra notRealizing
              have properMem : proper ∈ candidates := by
                simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
                exact ⟨properSubset.subset.trans familyFacts.1,
                  ⟨properNonempty, notRealizing⟩⟩
              exact properSubset.2
                (selectedFacts.2 proper properMem properSubset.subset)
            have overlapWitness : ∃ left ∈ family, ∃ right ∈ family,
                left ≠ right ∧ system.toSkeletonModel.Overlaps left right := by
              by_contra absent
              push Not at absent
              have separated : system.toSkeletonModel.PairwiseSeparated family := by
                intro left leftMem right rightMem different overlap
                exact absent left leftMem right rightMem different overlap
              exact minimal.1.2 (factorization.separated family separated)
            have connected :
                Graph.SupportComponents.Connected.ConnectedOn object
                  (system.overlapSupport family) := by
              let model := system.toSkeletonModel
              have familyNonempty : family.Nonempty := minimal.1.1
              have notRealizing :
                  ¬ model.RealizingOrder (LengthOK := data.LengthOK) family := by
                simpa [model, PairOverlapSystem.realizingOrder] using minimal.1.2
              have properRealizing : ∀ proper, proper ⊂ family → proper.Nonempty →
                  model.RealizingOrder (LengthOK := data.LengthOK) proper := by
                intro proper properSubset properNonempty
                simpa [model, PairOverlapSystem.realizingOrder] using
                  minimal.2 proper properSubset properNonempty
              let support := model.responseSupportUnion family
              have supportNonempty : support.Nonempty := by
                obtain ⟨pair, pairMem⟩ := familyNonempty
                obtain ⟨vertex, vertexMem⟩ :=
                  (model.responseSupport_connected pair).1
                refine ⟨vertex, ?_⟩
                change vertex ∈ model.responseSupportUnion family
                exact Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩
              change Graph.SupportComponents.Connected.ConnectedOn object support
              by_contra disconnected
              have componentEqOfPath
                  {left right : object.Vertex}
                  (leftMem : left ∈ support) (rightMem : right ∈ support)
                  (path : object.graph.Walk left right)
                  (inside : ∀ vertex ∈ path.support, vertex ∈ support) :
                  Graph.SupportComponents.Connected.componentOf object support
                      ⟨left, leftMem⟩ =
                    Graph.SupportComponents.Connected.componentOf object support
                      ⟨right, rightMem⟩ := by
                apply SimpleGraph.ConnectedComponent.sound
                let induced := path.induce (↑support) inside
                exact ⟨by
                  simpa [Graph.SupportComponents.Connected.InducedObject,
                    Graph.FiniteObject.induce] using induced⟩
              let anchor (pair : {pair // pair ∈ system.first.pairSet}) :
                  object.Vertex :=
                Classical.choose (model.responseSupport_connected pair).1
              have anchorMem (pair : {pair // pair ∈ system.first.pairSet}) :
                  anchor pair ∈ model.responseSupport pair :=
                Classical.choose_spec (model.responseSupport_connected pair).1
              have responseSubsetOwnComponent
                  (pair : {pair // pair ∈ system.first.pairSet})
                  (pairMem : pair ∈ family) :
                  model.responseSupport pair ⊆
                    Graph.SupportComponents.Connected.members object support
                      (Graph.SupportComponents.Connected.componentOf object support
                        ⟨anchor pair, by
                          simpa [support, model, PairOverlapSystem.toSkeletonModel,
                            Graph.SparsePairSkeletonModel.responseSupportUnion] using
                              (Finset.mem_biUnion.mpr
                                ⟨pair, pairMem, anchorMem pair⟩)⟩) := by
                intro vertex vertexMem
                have anchorSupport : anchor pair ∈ support := by
                  simpa [support, model, PairOverlapSystem.toSkeletonModel,
                    Graph.SparsePairSkeletonModel.responseSupportUnion] using
                      (Finset.mem_biUnion.mpr
                        ⟨pair, pairMem, anchorMem pair⟩)
                have vertexSupport : vertex ∈ support := by
                  simpa [support, model, PairOverlapSystem.toSkeletonModel,
                    Graph.SparsePairSkeletonModel.responseSupportUnion] using
                      (Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩)
                obtain ⟨path, _path, insidePair⟩ :=
                  (model.responseSupport_connected pair).2
                    (anchorMem pair) vertexMem
                apply (Graph.SupportComponents.Connected.mem_members_iff
                  object support _ vertex).mpr
                refine ⟨vertexSupport, ?_⟩
                exact (componentEqOfPath anchorSupport vertexSupport path
                  (fun current currentMem => by
                    simpa [support, model, PairOverlapSystem.toSkeletonModel,
                      Graph.SparsePairSkeletonModel.responseSupportUnion] using
                        (Finset.mem_biUnion.mpr
                          ⟨pair, pairMem, insidePair current currentMem⟩))).symm
              let rootPair := Classical.choose familyNonempty
              have rootPairMem : rootPair ∈ family :=
                Classical.choose_spec familyNonempty
              have rootAnchorSupport : anchor rootPair ∈ support := by
                simpa [support, model, PairOverlapSystem.toSkeletonModel,
                  Graph.SparsePairSkeletonModel.responseSupportUnion] using
                    (Finset.mem_biUnion.mpr
                      ⟨rootPair, rootPairMem, anchorMem rootPair⟩)
              let rootComponent :=
                Graph.SupportComponents.Connected.componentOf object support
                  ⟨anchor rootPair, rootAnchorSupport⟩
              let rootMembers :=
                Graph.SupportComponents.Connected.members object support rootComponent
              have rootComponentMem : rootComponent ∈
                  Graph.SupportComponents.Connected.order object support := by
                obtain ⟨component, componentMem, anchorInComponent⟩ :=
                  (Graph.SupportComponents.Connected.mem_support_iff_mem_component
                    object support (anchor rootPair)).mp rootAnchorSupport
                have equal : rootComponent = component := by
                  exact (Graph.SupportComponents.Connected.mem_members_iff
                    object support component (anchor rootPair)).mp
                      anchorInComponent |>.2
                simpa [equal] using componentMem
              have rootConnected :
                  Graph.SupportComponents.Connected.ConnectedOn object rootMembers :=
                Graph.SupportComponents.Connected.connectedOn_of_mem_order
                  object support rootComponentMem
              have rootMembersSubset : rootMembers ⊆ support := by
                intro vertex vertexMem
                exact (Graph.SupportComponents.Connected.mem_members_iff
                  object support rootComponent vertex).mp vertexMem |>.1
              have rootResponseSubset :
                  model.responseSupport rootPair ⊆ rootMembers := by
                simpa [rootComponent, rootMembers] using
                  responseSubsetOwnComponent rootPair rootPairMem
              have responseSubsetRootOfCommon
                  (pair : {pair // pair ∈ system.first.pairSet})
                  (pairMem : pair ∈ family)
                  {common : object.Vertex}
                  (commonPair : common ∈ model.responseSupport pair)
                  (commonRoot : common ∈ rootMembers) :
                  model.responseSupport pair ⊆ rootMembers := by
                intro vertex vertexMem
                have commonSupport : common ∈ support :=
                  rootMembersSubset commonRoot
                have vertexSupport : vertex ∈ support := by
                  simpa [support, model, PairOverlapSystem.toSkeletonModel,
                    Graph.SparsePairSkeletonModel.responseSupportUnion] using
                      (Finset.mem_biUnion.mpr ⟨pair, pairMem, vertexMem⟩)
                obtain ⟨path, _path, insidePair⟩ :=
                  (model.responseSupport_connected pair).2 commonPair vertexMem
                have commonComponent :
                    Graph.SupportComponents.Connected.componentOf object support
                        ⟨common, commonSupport⟩ = rootComponent :=
                  (Graph.SupportComponents.Connected.mem_members_iff
                    object support rootComponent common).mp commonRoot |>.2
                have pathComponents :=
                  componentEqOfPath commonSupport vertexSupport path
                    (fun current currentMem => by
                      simpa [support, model, PairOverlapSystem.toSkeletonModel,
                        Graph.SparsePairSkeletonModel.responseSupportUnion] using
                          (Finset.mem_biUnion.mpr
                            ⟨pair, pairMem, insidePair current currentMem⟩))
                apply (Graph.SupportComponents.Connected.mem_members_iff
                  object support rootComponent vertex).mpr
                exact ⟨vertexSupport,
                  pathComponents.symm.trans commonComponent⟩
              have outsideRoot : ∃ pair ∈ family,
                  ¬ model.responseSupport pair ⊆ rootMembers := by
                by_contra absent
                push Not at absent
                have supportSubset : support ⊆ rootMembers := by
                  intro vertex vertexMem
                  have inUnion :
                      vertex ∈ family.biUnion model.responseSupport := by
                    simpa [support, model, PairOverlapSystem.toSkeletonModel,
                      Graph.SparsePairSkeletonModel.responseSupportUnion] using
                        vertexMem
                  obtain ⟨pair, pairMem, inResponse⟩ :=
                    Finset.mem_biUnion.mp inUnion
                  exact absent pair pairMem inResponse
                have supportEq : support = rootMembers :=
                  Finset.Subset.antisymm supportSubset rootMembersSubset
                apply disconnected
                simpa [supportEq] using rootConnected
              let left : Finset {pair // pair ∈ system.first.pairSet} :=
                family.filter fun pair => model.responseSupport pair ⊆ rootMembers
              let right : Finset {pair // pair ∈ system.first.pairSet} :=
                family \ left
              have leftSubset : left ⊆ family := Finset.filter_subset _ _
              have rightSubset : right ⊆ family := Finset.sdiff_subset
              have leftNonempty : left.Nonempty := by
                exact ⟨rootPair, by
                  simp [left, rootPairMem, rootResponseSubset]⟩
              have rightNonempty : right.Nonempty := by
                obtain ⟨pair, pairMem, notSubset⟩ := outsideRoot
                exact ⟨pair, by simp [right, left, pairMem, notSubset]⟩
              have disjoint : Disjoint left right := by
                apply Finset.disjoint_left.mpr
                intro pair pairLeft pairRight
                exact (Finset.mem_sdiff.mp pairRight).2 pairLeft
              have noCross : ∀ leftPair, leftPair ∈ left →
                  ∀ rightPair, rightPair ∈ right →
                    ¬ model.Overlaps leftPair rightPair := by
                intro leftPair leftMem rightPair rightMem overlap
                have leftFacts := Finset.mem_filter.mp leftMem
                have rightFacts := Finset.mem_sdiff.mp rightMem
                obtain ⟨vertex, vertexLeft, vertexRight,
                    _leftPort, _rightPort⟩ := overlap
                have rightSubsetRoot := responseSubsetRootOfCommon rightPair
                  (rightSubset rightMem) vertexRight (leftFacts.2 vertexLeft)
                exact rightFacts.2 (Finset.mem_filter.mpr
                  ⟨rightSubset rightMem, rightSubsetRoot⟩)
              have leftProper : left ⊂ family := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨leftSubset, ?_⟩
                intro equal
                obtain ⟨pair, pairRight⟩ := rightNonempty
                exact (Finset.mem_sdiff.mp pairRight).2
                  (equal ▸ rightSubset pairRight)
              have rightProper : right ⊂ family := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨rightSubset, ?_⟩
                intro equal
                obtain ⟨pair, pairLeft⟩ := leftNonempty
                exact (Finset.mem_sdiff.mp
                  (equal ▸ leftSubset pairLeft)).2 pairLeft
              have unionEq : left ∪ right = family := by
                change left ∪ (family \ left) = family
                rw [Finset.union_comm]
                exact Finset.sdiff_union_of_subset leftSubset
              apply notRealizing
              have joined := factorization.concatenate left right
                leftNonempty rightNonempty disjoint noCross
                (properRealizing left leftProper leftNonempty)
                (properRealizing right rightProper rightNonempty)
              have familyUnionEq : model.familyUnion left right = family := by
                unfold Graph.SparsePairSkeletonModel.familyUnion
                exact unionEq
              rw [familyUnionEq] at joined
              exact joined
            exact
              { system := system
                family := family
                factorization := factorization
                minimal := minimal
                overlapWitness := overlapWitness
                connected := connected }))
          inputs.current.object
          (inputs.get (K .pairConditionalFactorization)).down
      .cons (key := K .pairFailureOverlap)
        (show Value BranchState Presentation presentation data
            .pairFailureOverlap inputs.current from ⟨⟨overlap⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine

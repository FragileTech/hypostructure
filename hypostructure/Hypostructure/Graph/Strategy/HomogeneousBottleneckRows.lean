import Hypostructure.Graph.Strategy.SpineRows
import Hypostructure.Graph.NamedSurplusExits

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Classify the concrete overload witness already carried by the incoming
ledger according to whether its token lies in the window-incidence class. -/
noncomputable def windowOverloadClassDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .sparsePressureOverload) known]
    (windowFresh : K .windowClassOverload ∉ known)
    (outsideFresh : K .windowClassAbsent ∉ known) :
    Decision (K .windowClassOverload) (K .windowClassAbsent) previous :=
  Decision.run previous (K .windowClassOverload) (K .windowClassAbsent)
    `Hypostructure.Graph.Strategy.Spine.windowOverloadClassDichotomy
    (Classical.choice (show Nonempty
        ((K .windowClassOverload).At current ⊕
          (K .windowClassAbsent).At current) from by
      obtain ⟨declared, ledger, routingLabelBound, token, role, tokenMem,
        _selected, rest⟩ := (previous.get (K .sparsePressureOverload)).down
      cases classified : ledger.presented.tokenClass token with
      | windowIncidence =>
          exact ⟨.inl ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, classified, rest⟩⟩
      | remainderSurplus =>
          exact ⟨.inr ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, by simpa [classified], rest⟩⟩
      | primitiveCarrier =>
          exact ⟨.inr ⟨declared, ledger, routingLabelBound, token, role,
            tokenMem, by simpa [classified], rest⟩⟩))
    windowFresh outsideFresh

@[reducible] noncomputable def pressureSpineSurplusEstimateRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pressureSpineSurplusEstimate
    { Requires := [K .sparsePressureNearCubic]
      Produces := [K .spineSurplusEstimate]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .spineSurplusEstimate)
        (show Value BranchState Presentation presentation data
            .spineSurplusEstimate inputs.current from
          ⟨(inputs.get (K .sparsePressureNearCubic)).down⟩)
        .nil)

@[reducible] noncomputable def sparseSurplusSurvivorRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.sparseSurplusSurvivor
    { Requires := [K .selection, K .uncompressible]
      Produces := [K .sparseSurplusSurvivor]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let _uncompressible := (inputs.get (K .uncompressible)).down
      .cons (key := K .sparseSurplusSurvivor)
        (show Value BranchState Presentation presentation data
            .sparseSurplusSurvivor inputs.current from
          ⟨⟨Graph.survives_of_selection selection.1 selection.2 uncompressible,
            fun support replacement =>
              Graph.Strategy.InterfaceReplacement.not_replacementSupport
                (Graph.MinimumDegreeAtLeast data.threshold) BranchState
                (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
                Presentation presentation
                (Core.Target.ofPredicate _
                  (Graph.HasCycleWithLength data.LengthOK))
                ((Graph.cycleTargetInterface data.LengthOK).coreInvariantWithPresentation
                  (Graph.MinimumDegreeAtLeast data.threshold) BranchState
                  Presentation presentation
                  (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
                { G := inputs.current.object,
                  baseline := inputs.current.baseline,
                  state := inputs.current.branchState,
                  avoids := selection.1,
                  minimal := selection.2 }
                support replacement⟩⟩)
        .nil)

/-- Node `[144]`: route every declared same-token bottleneck of the current
residual.  Both hypotheses are read from the incoming exact ledger. -/
@[reducible] noncomputable def bottleneckRoutingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.bottleneckRouting
    { Requires := [K .selection, K .uncompressible]
      Produces := [K .bottleneckRouting]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let selection := (inputs.get (K .selection)).down
      let uncompressible := (inputs.get (K .uncompressible)).down
      .cons (key := K .bottleneckRouting)
        (show Value BranchState Presentation presentation data
            .bottleneckRouting inputs.current from
          ⟨by
            simp only [Holds]
            intro HighDegree Absorbing bottleneck windowFree
            exact bottleneck.outcome selection.1 uncompressible windowFree⟩)
        .nil)

/-- Node `[144]`, survivor arm: eliminate the absorbed outcome locally and
append the resulting Type-B handoff fact to the same ledger. -/
@[reducible] noncomputable def typeBHandoffRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.typeBHandoff
    { Requires := [K .bottleneckRouting, K .sparseSurplusSurvivor]
      Produces := [K .typeBHandoff]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let routed := (inputs.get (K .bottleneckRouting)).down
      let survivor := (inputs.get (K .sparseSurplusSurvivor)).down
      .cons (key := K .typeBHandoff)
        (show Value BranchState Presentation presentation data
            .typeBHandoff inputs.current from
          ⟨by
            classical
            simp only [Holds] at routed ⊢
            intro HighDegree Absorbing bottleneck windowFree internal baseline
              contextEquivalent
            rcases routed HighDegree Absorbing bottleneck windowFree with
              absorbed | handoff
            · exfalso
              apply survivor.1
              rcases absorbed with defect | complete | delocalizes
              · obtain ⟨context, separated⟩ := defect
                exact absurd (contextEquivalent context) separated
              · refine .compression bottleneck.separation.switchSupport
                  ⟨bottleneck.separation.switchConnected,
                    bottleneck.separation.switchProper,
                    bottleneck.reading.quotient, ?_, baseline,
                    bottleneck.reading.lexicographicallySmaller, ?_⟩
                · have registered := bottleneck.reading.registered internal
                    bottleneck.reading.reduced
                    bottleneck.reading.reduced_ssubset.subset
                  exact registered.trans rfl
                · intro context
                  have equivalence := complete.2 context
                  rw [bottleneck.reading.baseIsPiece] at equivalence
                  simpa [Graph.DecoratedHandoff.Separation.atom] using equivalence
              · obtain ⟨representative, smaller, baselineObject, transfer⟩ :=
                  delocalizes
                exact .delocalization representative smaller baselineObject
                  transfer
            · exact handoff⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine

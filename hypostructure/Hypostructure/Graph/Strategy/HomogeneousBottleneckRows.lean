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

/-- Node `[140]`: the geometric audit of the concrete window-incidence class
selected by `[139]`.  The class fact fixes the routed arm; the audit itself is
the canonical counted-label theorem at the current object. -/
@[reducible] noncomputable def windowIncidenceAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.windowIncidenceAudit
    { Requires := [K .windowClassOverload]
      Produces := [K .windowIncidenceAudit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _selectedClass := inputs.get (K .windowClassOverload)
      .cons (key := K .windowIncidenceAudit)
        (show Value BranchState Presentation presentation data
            .windowIncidenceAudit inputs.current from
          ⟨Graph.classAuditStatement inputs.current.object data.threshold
            data.windowOrder
            (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
              (Graph.WindowCurvature.Label data.windowOrder))
            .windowIncidence⟩)
        .nil)

/-- Node `[142]`: the geometric audit of the concrete remainder-surplus class
selected by `[141]`. -/
@[reducible] noncomputable def remainderSurplusAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.remainderSurplusAudit
    { Requires := [K .remainderClassOverload]
      Produces := [K .remainderSurplusAudit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _selectedClass := inputs.get (K .remainderClassOverload)
      .cons (key := K .remainderSurplusAudit)
        (show Value BranchState Presentation presentation data
            .remainderSurplusAudit inputs.current from
          ⟨Graph.classAuditStatement inputs.current.object data.threshold
            data.windowOrder
            (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
              (Graph.WindowCurvature.Label data.windowOrder))
            .remainderSurplus⟩)
        .nil)

/-- Node `[143]`: the geometric audit of the concrete primitive-carrier class
selected after the two negative class tests. -/
@[reducible] noncomputable def primitiveCarrierAuditRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveCarrierAudit
    { Requires := [K .primitiveClassOverload]
      Produces := [K .primitiveCarrierAudit]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let _selectedClass := inputs.get (K .primitiveClassOverload)
      .cons (key := K .primitiveCarrierAudit)
        (show Value BranchState Presentation presentation data
            .primitiveCarrierAudit inputs.current from
          ⟨Graph.classAuditStatement inputs.current.object data.threshold
            data.windowOrder
            (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
              (Graph.WindowCurvature.Label data.windowOrder))
            .primitiveCarrier⟩)
        .nil)

/-- Node `[143]`: normalize node `[141]`'s literal no-remainder residual to the
canonical primitive-class verdict consumed by the audit. -/
@[reducible] noncomputable def primitiveClassOverloadRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.primitiveClassOverload
    { Requires := [K .remainderClassAbsent]
      Produces := [K .primitiveClassOverload]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .primitiveClassOverload)
        ⟨(inputs.get (K .remainderClassAbsent)).down⟩ .nil)

/-- Node `[144]`, `cor:homogeneous-same-token-caps-close`: on the literal
fixed-caps residual, spend the already registered sparse slack identity and
publish the manuscript's homogeneous-cap closure statement. -/
@[reducible] noncomputable def homogeneousCapsCloseRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.homogeneousCapsClose
    { Requires := [K .homogeneousCapsHold, K .sparseSlackSurplus]
      Produces := [K .homogeneousBottleneck]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .homogeneousBottleneck)
        (show Value BranchState Presentation presentation data
            .homogeneousBottleneck inputs.current from
          ⟨Graph.homogeneousCapsCloseStatement inputs.current.object
            (inputs.get (K .homogeneousCapsHold)).down
            (inputs.get (K .sparseSlackSurplus)).down⟩)
        .nil)

/-- Node `[125]`, `def:named-surplus-exits`: the literal sparse-exit/survivor
dichotomy on the incoming residual.  The two arms remain separate exact-ledger
histories. -/
noncomputable def sparseSurplusExitDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (exitFresh : K .sparsePairExit ∉ known)
    (survivorFresh : K .sparseSurplusSurvivor ∉ known) :
    Decision (K .sparsePairExit) (K .sparseSurplusSurvivor) previous :=
  Decision.run previous (K .sparsePairExit) (K .sparseSurplusSurvivor)
    `Hypostructure.Graph.Strategy.Spine.sparseSurplusExitDichotomy
    (Classical.choice (show Nonempty
        ((K .sparsePairExit).At current ⊕
          (K .sparseSurplusSurvivor).At current) from by
      classical
      by_cases exit : Graph.SparseSurplusExit
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) data.LengthOK current.object
      · exact ⟨.inl ⟨exit⟩⟩
      · exact ⟨.inr ⟨exit⟩⟩))
    exitFresh survivorFresh

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
      let uncompressible := (inputs.get (K .uncompressible)).down.1
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
              apply survivor
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
                  intro target
                  have targetFull := equivalence.mp target
                  change Graph.HasCycleWithLength data.LengthOK
                    (Graph.glue
                      (bottleneck.reading.state bottleneck.reading.base)
                      context) at targetFull
                  rw [bottleneck.reading.baseIsPiece] at targetFull
                  exact targetFull
              · obtain ⟨representative, smaller, baselineObject, transfer⟩ :=
                  delocalizes
                exact .delocalization representative smaller baselineObject
                  transfer
            · exact handoff⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine

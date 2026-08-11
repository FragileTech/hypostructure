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
      let uncompressible := (inputs.get (K .uncompressible)).down
      .cons (key := K .sparseSurplusSurvivor)
        (show Value BranchState Presentation presentation data
            .sparseSurplusSurvivor inputs.current from
          ⟨⟨Graph.survives_of_selection selection.1 selection.2 uncompressible,
            fun _support replacement =>
              not_globalBarrierReading (BranchState := BranchState)
                (Presentation := Presentation) (presentation := presentation)
                (data := data) inputs.current selection.1 selection.2
                (Or.inl replacement)⟩⟩)
        .nil)

end Hypostructure.Graph.Strategy.Spine

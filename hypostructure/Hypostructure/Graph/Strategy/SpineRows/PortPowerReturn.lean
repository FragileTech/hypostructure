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

/-! ## Power-of-two port returns (no manuscript label; not a manuscript statement)

For each eligible completion port of the exact saturated Type A support, apply
the ledger's contraction-criticality fact to the oriented port edge and delete
that edge from the resulting cycle.  The same severed path becomes an anchored
return without changing its exact dyadic length. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def portPowerReturnRow :
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
    `Hypostructure.Graph.Strategy.Spine.portPowerReturn
    { Requires := [K .typeASaturatedReceiver, K .contractionCritical]
      Produces := [K .portPowerReturn]
      requiresUnique := by simp [K_eq_iff]
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let saturated := (inputs.get (K .typeASaturatedReceiver)).down
      let contractionCritical := (inputs.get (K .contractionCritical)).down
      .cons (key := K .portPowerReturn) ⟨by
        obtain ⟨packing, _canonical, valid, maximal, component, present, negative, zero,
          selectedReceiver, selectedIsReceiver, selectedSaturated⟩ := saturated
        let piece := inputs.current.object.pieceSupport
          (inputs.current.object.remainderSupport packing) component
        refine ⟨packing, valid, maximal, component, present, negative, zero,
          ⟨selectedReceiver, selectedIsReceiver, selectedSaturated⟩, ?_⟩
        intro receiver receiverIsReceiver outside outsideMem noCommonCubic
        have adjacent : inputs.current.object.graph.Adj receiver outside :=
          (Graph.VisibleEntry.mem_completionPorts.mp outsideMem).1
        let contraction : Graph.EdgeContraction inputs.current.object :=
          ⟨outside, receiver, adjacent.symm⟩
        obtain ⟨path, exponent, lower, pathLength⟩ :=
          contractionCritical contraction (by
            intro common outsideCommon receiverCommon
            exact noCommonCubic common receiverCommon outsideCommon)
        let return' := Graph.VisibleEntry.anchoredReturnOfSeveredPath
          adjacent path
        refine ⟨return', exponent, lower, ?_⟩
        simpa [return', Graph.VisibleEntry.anchoredReturnOfSeveredPath] using
          pathLength⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine

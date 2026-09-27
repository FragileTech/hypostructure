import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.SpineWindows

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[15]`: `G` is `P₁₃`-free?

The yes key is `windowFree` (the object has no induced window of the registered
order), the no key `windowPresent` (it has one); the two are exact complements
on the same object.  The yes arm closes at node `[16]`: the cited closure law
`thm:p13free`, read at G from `K .spinePresentationLaws`, gives G an accepted
cycle (`K .hssTargetCycle`), which the selection denies (`cor:p13-exists`).  The
closure is the framework's, `runAndCloseIncompatible` against `K .selection`. -/

/-- **Node `[15]`: `G` is `P₁₃`-free?** -/
noncomputable def windowFreeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (freeFresh : K .windowFree ∉ known)
    (presentFresh : K .windowPresent ∉ known) :
    Decision (K .windowFree) (K .windowPresent) previous :=
  Decision.run previous (K .windowFree) (K .windowPresent)
    `Hypostructure.Graph.Strategy.Spine.windowFreeDichotomy
    (Classical.choice (show Nonempty
        ((K .windowFree).At current ⊕ (K .windowPresent).At current) from by
      by_cases present : Graph.HasInducedPath current.object data.windowOrder
      · exact ⟨.inr ⟨present⟩⟩
      · exact ⟨.inl ⟨present⟩⟩))
    freeFresh presentFresh

/-- **Node `[16]`: the HSS theorem gives a target cycle.**  On the yes arm of
node `[15]` the row reads the cited closure law `thm:p13free` at G
(`K .spinePresentationLaws`) and G's window-freeness (`K .windowFree`), and
publishes that G has an accepted cycle. -/
@[reducible] noncomputable def hssTargetCycleRow :
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
    `Hypostructure.Graph.Strategy.Spine.hssTargetCycle
    { Requires := [K .spinePresentationLaws, K .windowFree]
      Produces := [K .hssTargetCycle]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .hssTargetCycle)
        ⟨(inputs.get (K .spinePresentationLaws)).down.1 inputs.current.baseline
          (inputs.get (K .windowFree)).down⟩
        .nil)
    0 0

/-- **Node `[16]`, the terminal.**  G's accepted cycle contradicts the
selection's target avoidance. -/
noncomputable instance instIncompatibleSelectionHssTargetCycle :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .hssTargetCycle) where
  contradiction := fun _input selection cycle => selection.down.1 cycle.down

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[17]`: the maximal induced-window packing

Node `[15]`'s no arm says the selected object contains an induced window of the
registered order, so the packing number is positive and some vertex-disjoint
family attains it.

Maximality is not assumed: `exists_mem_not_disjoint_of_card_eq` derives it from
attaining the maximum, because a window disjoint from every member could be
added.  The family itself never leaves this row -- what the ledger records is
the number, which is a function of the object, and the statement that a family
attains it. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def obstructionPackingRow :
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
    `Hypostructure.Graph.Strategy.Spine.obstructionPacking
    { Requires := [K .windowPresent]
      Produces := [K .maximalPacking]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .maximalPacking)
        ⟨Contracts.Spine.maximalPacking_of_windowPresent data.toParameters
          inputs.current.object (inputs.get (K .windowPresent)).down⟩
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine

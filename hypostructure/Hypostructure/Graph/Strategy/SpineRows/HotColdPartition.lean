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

/-! ## Node `[22]`: the canonical hot/cold partition

`def:cold-window-ledger`.  The manuscript fixes the maximal packing once (the
lexicographically first object with the extremal property, `lem:skeleton-dominates`)
and splits it into hot and cold windows.  `canonicalWindowPacking` is that fixed
packing, so its defining specification is the whole input of the split: the row
reads no predecessor fact and re-proves nothing.  `hot` and `cold` are the
canonical filters inside the ledger proposition; they are not callback arguments
or mutable routing state. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def hotColdPartitionRow :
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
    `Hypostructure.Graph.Strategy.Spine.hotColdPartition
    { Requires := []
      Produces := [K .hotColdPartition]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .hotColdPartition)
        (show Value BranchState Presentation presentation data
            .hotColdPartition inputs.current from
          ⟨by
            classical
            let object := inputs.current.object
            let packing := canonicalWindowPacking data object
            have packingFacts :
                object.IsWindowPacking data.windowOrder packing ∧
                  packing.card = object.windowPackingNumber data.windowOrder :=
              Classical.choose_spec
                (object.exists_windowPacking_card_eq data.windowOrder)
            let hot := canonicalHotWindows data object
            let cold := canonicalColdWindows data object
            have hotFacts :
                hot ⊆ packing ∧
                  (WindowFamilyRealized data object hot ∨
                    (hot = ∅ ∧ ¬ WindowFamilyRealized data object ∅)) ∧
                  ∀ other : Finset (Finset object.Vertex), other ⊆ packing →
                    WindowFamilyRealized data object other →
                      other.card ≤ hot.card :=
              Classical.choose_spec (exists_maximal_windowFamilyRealized data object)
            show IsHotColdWindowPartition data object packing hot cold
            refine ⟨packingFacts.1, packingFacts.2, ?_, hotFacts, ?_, ?_, ?_⟩
            · intro support window
              exact object.exists_mem_not_disjoint_of_card_eq
                data.windowOrder_pos packingFacts.1 packingFacts.2 window
            · intro window
              simp [cold, packing, hot, canonicalColdWindows]
            · exact Finset.disjoint_sdiff
            · intro window
              constructor
              · intro member
                by_cases inHot : window ∈ hot
                · exact Or.inl inHot
                · exact Or.inr (by
                    simp [cold, packing, hot, canonicalColdWindows, member, inHot])
              · intro member
                rcases member with member | member
                · exact hotFacts.1 member
                · exact (Finset.mem_sdiff.mp member).1⟩)
        .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine

import Hypostructure.Core.Finite.MaximalSelection

/-!
# Canonical obstruction-packing data

This lower Core module owns the domain-neutral maximal-packing certificate and
its finite cardinality theorem.  It is deliberately independent of the CT1
executable strategy so other semantic producers can consume an exact packing
without importing the Strategy compiler.
-/

namespace Hypostructure.Core.Strategy.ObstructionPackingClosure

open scoped BigOperators

universe uData

/-- Canonical maximal-packing facts, independent of the implementation used
to choose the selected family. -/
structure Packing {Occurrence : Type uData}
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop) where
  selected : List Occurrence
  selected_nodup : selected.Nodup
  selected_mem_schedule : ∀ ⦃item⦄, item ∈ selected → item ∈ schedule.values
  pairwiseCompatible : ∀ ⦃left right⦄,
    left ∈ selected → right ∈ selected → left ≠ right → ¬ conflict left right
  maximal : ∀ item, item ∈ schedule.values →
    ∃ selectedItem ∈ selected, conflict item selectedItem ∨ item = selectedItem

/-- A live obstruction-packing result.  The nonempty certificate is produced
from CT1's actual hit arm and travels with the exact canonical packing. -/
structure NonemptyPacking {Occurrence : Type uData}
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop) where
  packing : Packing schedule conflict
  selected_nonempty : packing.selected ≠ []

namespace Packing

variable {Occurrence : Type uData}

theorem selected_nonempty_of_schedule_member
    (packing : Packing schedule conflict)
    {item : Occurrence} (member : item ∈ schedule.values) :
    packing.selected ≠ [] := by
  obtain ⟨selectedItem, selectedMember, _⟩ := packing.maximal item member
  exact List.ne_nil_of_mem selectedMember

def admissible (conflict : Occurrence → Occurrence → Prop)
    (selected : Finset Occurrence) : Prop :=
  ∀ ⦃left right⦄, left ∈ selected → right ∈ selected → left ≠ right →
    ¬ conflict left right

noncomputable def admissibleSets
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict) :
    Finset (Finset Occurrence) := by
  letI : DecidableEq Occurrence := schedule.decEq
  letI : DecidablePred (admissible conflict) := Classical.decPred _
  exact schedule.toFinset.powerset.filter (admissible conflict)

theorem admissibleSets_nonempty
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict) :
    (admissibleSets schedule conflict decConflict).Nonempty := by
  letI : DecidableEq Occurrence := schedule.decEq
  exact ⟨∅, by simp [admissibleSets, admissible]⟩

noncomputable def maximalSet
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict) : Finset Occurrence := by
  letI : DecidableEq Occurrence := schedule.decEq
  letI : DecidableEq (Finset Occurrence) := Classical.decEq _
  exact (Core.Finite.MaximalSelection.chooseSelection
    (admissibleSets schedule conflict decConflict)
    (admissibleSets_nonempty schedule conflict decConflict)).value

theorem maximalSet_mem
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict) :
    maximalSet schedule conflict decConflict ∈
      admissibleSets schedule conflict decConflict := by
  letI : DecidableEq Occurrence := schedule.decEq
  letI : DecidableEq (Finset Occurrence) := Classical.decEq _
  exact (Core.Finite.MaximalSelection.chooseSelection
    (admissibleSets schedule conflict decConflict)
    (admissibleSets_nonempty schedule conflict decConflict)).mem

theorem maximalSet_maximal
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict) :
    Maximal (fun selected =>
      selected ∈ admissibleSets schedule conflict decConflict)
      (maximalSet schedule conflict decConflict) := by
  letI : DecidableEq Occurrence := schedule.decEq
  letI : DecidableEq (Finset Occurrence) := Classical.decEq _
  exact (Core.Finite.MaximalSelection.chooseSelection
    (admissibleSets schedule conflict decConflict)
    (admissibleSets_nonempty schedule conflict decConflict)).maximal

noncomputable def canonical
    (schedule : Core.Finite.Enumeration Occurrence)
    (conflict : Occurrence → Occurrence → Prop)
    (decConflict : DecidableRel conflict)
    (symmetric : Symmetric conflict) :
    Packing schedule conflict := by
  classical
  let selected := maximalSet schedule conflict decConflict
  have selectedMem := maximalSet_mem schedule conflict decConflict
  have selectedAdmissible : admissible conflict selected :=
    (Finset.mem_filter.mp selectedMem).2
  refine {
    selected := selected.toList
    selected_nodup := selected.nodup_toList
    selected_mem_schedule := ?_
    pairwiseCompatible := ?_
    maximal := ?_
  }
  · intro item itemMem
    have itemMemSelected : item ∈ selected := Finset.mem_toList.mp itemMem
    have selectedSubset : selected ⊆ schedule.toFinset :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp selectedMem).1
    exact (Core.Finite.Enumeration.mem_toFinset schedule item).mp
      (selectedSubset itemMemSelected)
  · intro left right leftMem rightMem different
    exact selectedAdmissible
      (Finset.mem_toList.mp leftMem) (Finset.mem_toList.mp rightMem) different
  · intro item itemMem
    by_cases already : item ∈ selected
    · exact ⟨item, Finset.mem_toList.mpr already, Or.inr rfl⟩
    · by_contra absent
      push Not at absent
      have inserted :
          insert item selected ∈ admissibleSets schedule conflict decConflict := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powerset.mpr
          intro value valueMem
          simp only [Finset.mem_insert] at valueMem
          rcases valueMem with rfl | valueMem
          · exact (Core.Finite.Enumeration.mem_toFinset schedule _).mpr itemMem
          · exact (Finset.mem_powerset.mp
              (Finset.mem_filter.mp selectedMem).1) valueMem
        · intro left right leftMem rightMem different
          simp only [Finset.mem_insert] at leftMem rightMem
          rcases leftMem with rfl | leftMem <;>
            rcases rightMem with rfl | rightMem
          · exact (different rfl).elim
          · exact (absent right (Finset.mem_toList.mpr rightMem)).1
          · intro related
            exact (absent left (Finset.mem_toList.mpr leftMem)).1
              (symmetric related)
          · exact selectedAdmissible leftMem rightMem different
      have maximal := maximalSet_maximal schedule conflict decConflict
      have subset := maximal.2 inserted (Finset.subset_insert _ _)
      exact already (subset (Finset.mem_insert_self item selected))

/-! A maximal packing covers the source schedule by one selected occurrence
and its conflict neighbourhood. -/
theorem schedule_card_le_selected_mul
    (packing : Packing schedule conflict)
    (neighborhoodBound : Nat)
    (decConflict : DecidableRel conflict)
    (bound : ∀ selectedItem ∈ packing.selected,
      (schedule.toFinset.filter
        (fun item => conflict item selectedItem)).card ≤ neighborhoodBound) :
    schedule.card ≤ packing.selected.length * (neighborhoodBound + 1) := by
  classical
  letI : DecidableRel conflict := decConflict
  let selectedSet := packing.selected.toFinset
  let cover := fun selectedItem =>
    insert selectedItem
      (schedule.toFinset.filter (fun item => conflict item selectedItem))
  have cover_subset : schedule.toFinset ⊆ selectedSet.biUnion cover := by
    intro item item_mem
    obtain ⟨selectedItem, selected_mem, conflict_or_equal⟩ :=
      packing.maximal item
        ((Core.Finite.Enumeration.mem_toFinset schedule item).mp item_mem)
    refine Finset.mem_biUnion.mpr ⟨selectedItem,
      (by simpa [selectedSet] using selected_mem), ?_⟩
    rcases conflict_or_equal with conflict_mem | rfl
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨item_mem, conflict_mem⟩)
    · simpa [cover] using (Finset.mem_insert_self item
        (schedule.toFinset.filter (fun item => conflict item item)))
  have each_cover_bound : ∀ selectedItem ∈ selectedSet,
      (cover selectedItem).card ≤ neighborhoodBound + 1 := by
    intro selectedItem selected_mem
    have selected_mem' : selectedItem ∈ packing.selected := by
      simpa [selectedSet] using selected_mem
    calc
      (cover selectedItem).card ≤
          (schedule.toFinset.filter
            (fun item => conflict item selectedItem)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ neighborhoodBound + 1 :=
        Nat.add_le_add_right (bound selectedItem selected_mem') 1
  calc
    schedule.card = schedule.toFinset.card :=
      (Core.Finite.Enumeration.card_toFinset schedule).symm
    _ ≤ (selectedSet.biUnion cover).card :=
      Finset.card_le_card cover_subset
    _ ≤ ∑ selectedItem ∈ selectedSet, (cover selectedItem).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _selectedItem ∈ selectedSet, (neighborhoodBound + 1) := by
      exact Finset.sum_le_sum fun selectedItem selected_mem =>
        each_cover_bound selectedItem selected_mem
    _ = selectedSet.card * (neighborhoodBound + 1) := by simp
    _ = packing.selected.length * (neighborhoodBound + 1) := by
      exact congrArg (fun n => n * (neighborhoodBound + 1))
        (List.toFinset_card_of_nodup packing.selected_nodup)

end Packing

end Hypostructure.Core.Strategy.ObstructionPackingClosure

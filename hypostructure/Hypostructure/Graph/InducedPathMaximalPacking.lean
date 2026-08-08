import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Finite.MaximalSelection
import Hypostructure.Graph.InducedPath

/-!
# Abstract maximal induced-path packing contracts

The graph layer exposes maximal packing data without fixing a theorem-specific
path length.  A consumer supplies a residual-owned selected list and the graph
semantics needed to prove disjointness/saturation; the framework interface
publishes only maximal-packing consequences and work accounting.
-/

namespace Hypostructure.Graph.InducedPathMaximalPacking

universe u

/-- A selected induced path occurrence in an arbitrary finite graph. -/
abbrev Window (object : FiniteObject.{u}) (order : Nat) :=
  SimpleGraph.pathGraph order ↪g object.graph

noncomputable def windowSchedule (object : FiniteObject.{u}) (order : Nat) :
    Core.Finite.Enumeration (Window object order) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : FinEnum (Fin order) := inferInstance
  letI : FinEnum (Fin order → object.Vertex) := inferInstance
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : FinEnum (Window object order) :=
    FinEnum.ofInjective (fun window : Window object order =>
      (window : Fin order → object.Vertex)) (by
        intro left right equal
        exact DFunLike.coe_injective equal)
  exact Core.Finite.Enumeration.ofFinEnum inferInstance


/-- Support of one induced-path occurrence. -/
def support (object : FiniteObject.{u}) (order : Nat)
    (window : Window object order) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (Finset.univ : Finset (Fin order)).image window

@[simp] theorem support_card (object : FiniteObject.{u}) (order : Nat)
    (window : Window object order) :
    (support object order window).card = order := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  unfold support
  calc
    (Finset.image (window : Fin order → object.Vertex) Finset.univ).card =
        (Finset.univ : Finset (Fin order)).card :=
      Finset.card_image_of_injective _ window.injective
    _ = order := by simp

/-! ## Canonical orientation of a packed P13 window -/

namespace P13

/-- Reversal of the thirteen path positions. -/
def reverseIndex (index : Fin 13) : Fin 13 :=
  ⟨12 - index.1, by omega⟩

@[simp] theorem reverseIndex_involutive (index : Fin 13) :
    reverseIndex (reverseIndex index) = index := by
  apply Fin.ext
  simp [reverseIndex]
  omega

theorem reverseIndex_injective : Function.Injective reverseIndex :=
  Function.LeftInverse.injective reverseIndex_involutive

theorem pathGraph_adj_reverse_iff (left right : Fin 13) :
    (SimpleGraph.pathGraph 13).Adj (reverseIndex left) (reverseIndex right) ↔
      (SimpleGraph.pathGraph 13).Adj left right := by
  rw [SimpleGraph.pathGraph_adj, SimpleGraph.pathGraph_adj]
  simp only [reverseIndex]
  omega

/-- The opposite orientation of one induced P13 occurrence. -/
def reverseWindow (window : Window object 13) : Window object 13 where
  toFun index := window (reverseIndex index)
  inj' := by
    intro left right equal
    exact reverseIndex_injective (window.injective equal)
  map_rel_iff' := by
    intro left right
    change object.graph.Adj (window (reverseIndex left))
        (window (reverseIndex right)) ↔ _
    rw [window.map_adj_iff, pathGraph_adj_reverse_iff]

@[simp] theorem reverseWindow_apply (window : Window object 13)
    (index : Fin 13) :
    reverseWindow window index = window (reverseIndex index) := rfl

/-- Reversing an occurrence does not change its embedded support. -/
theorem support_reverseWindow (window : Window object 13) :
    support object 13 (reverseWindow window) = support object 13 window := by
  classical
  ext vertex
  simp only [support, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨index, rfl⟩
    exact ⟨reverseIndex index, by simp⟩
  · rintro ⟨index, rfl⟩
    exact ⟨reverseIndex index, by simp⟩

/-- Valid ordered P13 placements with one fixed embedded support, in the
canonical finite embedding schedule. -/
noncomputable def placementCandidates (object : FiniteObject.{u})
    (windowSupport : Finset object.Vertex) : List (Window object 13) := by
  classical
  exact (windowSchedule object 13).values.filter fun window =>
    support object 13 window = windowSupport

/-- Membership in the support-filtered P13 schedule, without exposing the
filter implementation to the canonical selector proofs. -/
theorem mem_placementCandidates_iff (window : Window object 13)
    (windowSupport : Finset object.Vertex) :
    window ∈ placementCandidates object windowSupport ↔
      window ∈ (windowSchedule object 13).values ∧
        support object 13 window = windowSupport := by
  classical
  simp [placementCandidates]

/-- Every valid P13 occurrence appears in the candidate list for its support. -/
theorem mem_placementCandidates (window : Window object 13) :
    window ∈ placementCandidates object (support object 13 window) := by
  exact (mem_placementCandidates_iff window _).2
    ⟨by classical simp [windowSchedule], rfl⟩

/-- The lexicographically first valid ordered placement of an induced P13
support. -/
noncomputable def canonicalPlacement (window : Window object 13) :
    Window object 13 :=
  (placementCandidates object (support object 13 window)).headD window

/-- The selected placement is the first entry of the support-filtered schedule. -/
theorem canonicalPlacement_mem_candidates (window : Window object 13) :
    canonicalPlacement window ∈
      placementCandidates object (support object 13 window) := by
  classical
  have original := mem_placementCandidates (object := object) window
  cases candidatesEq : placementCandidates object (support object 13 window) with
  | nil => simp [candidatesEq] at original
  | cons first rest => simp [canonicalPlacement, candidatesEq]

/-- The selected placement is a member of the complete embedding schedule. -/
theorem canonicalPlacement_mem_schedule (window : Window object 13) :
    canonicalPlacement window ∈ (windowSchedule object 13).values := by
  exact (mem_placementCandidates_iff (canonicalPlacement window)
    (support object 13 window)).1
      (canonicalPlacement_mem_candidates (object := object) window) |>.1

/-- The selected placement has exactly the requested embedded support. -/
theorem canonicalPlacement_support (window : Window object 13) :
    support object 13 (canonicalPlacement window) = support object 13 window := by
  exact (mem_placementCandidates_iff (canonicalPlacement window)
    (support object 13 window)).1
      (canonicalPlacement_mem_candidates (object := object) window) |>.2

/-- Canonical placement depends only on the embedded support. -/
theorem canonicalPlacement_eq_of_support_eq (left right : Window object 13)
    (sameSupport : support object 13 left = support object 13 right) :
    canonicalPlacement left = canonicalPlacement right := by
  classical
  have original := mem_placementCandidates (object := object) left
  unfold canonicalPlacement
  rw [sameSupport]
  cases candidatesEq : placementCandidates object (support object 13 right) with
  | nil => simp [sameSupport, candidatesEq] at original
  | cons first rest => simp [candidatesEq]

/-- Reversal normalization: the two orientations select the same canonical
ordered placement. -/
theorem canonicalPlacement_reverse (window : Window object 13) :
    canonicalPlacement (reverseWindow window) = canonicalPlacement window :=
  canonicalPlacement_eq_of_support_eq _ _ (support_reverseWindow window)

end P13

def admissibleWindows (object : FiniteObject.{u}) (order : Nat)
    (windows : Finset (Window object order)) : Prop :=
  ∀ ⦃left right : Window object order⦄,
    left ∈ windows → right ∈ windows → left ≠ right →
      Disjoint (support object order left) (support object order right)

noncomputable def admissibleWindowSets (object : FiniteObject.{u}) (order : Nat) :
    Finset (Finset (Window object order)) := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : DecidablePred (admissibleWindows object order) := Classical.decPred _
  exact (windowSchedule object order).toFinset.powerset.filter
    (admissibleWindows object order)

theorem admissibleWindowSets_nonempty (object : FiniteObject.{u}) (order : Nat) :
    (admissibleWindowSets object order).Nonempty := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  refine ⟨∅, ?_⟩
  simp [admissibleWindowSets, admissibleWindows]

noncomputable def maximalWindowSelection (object : FiniteObject.{u}) (order : Nat) :
    @Core.Finite.MaximalSelection.Choice (Finset (Window object order))
      (Classical.decEq _) inferInstance inferInstance
      (admissibleWindowSets object order)
      (admissibleWindowSets_nonempty object order) := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  letI : DecidablePred (admissibleWindows object order) := Classical.decPred _
  exact Core.Finite.MaximalSelection.chooseSelection
    (admissibleWindowSets object order)
    (admissibleWindowSets_nonempty object order)

noncomputable def maximalWindowSet (object : FiniteObject.{u}) (order : Nat) :
    Finset (Window object order) := by
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  exact (maximalWindowSelection object order).value

theorem maximalWindowSet_mem (object : FiniteObject.{u}) (order : Nat) :
    maximalWindowSet object order ∈ admissibleWindowSets object order := by
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  exact (maximalWindowSelection object order).mem

theorem maximalWindowSet_admissible (object : FiniteObject.{u}) (order : Nat) :
    admissibleWindows object order (maximalWindowSet object order) := by
  letI : DecidableEq (Window object order) := Classical.decEq _
  letI : DecidablePred (admissibleWindows object order) := Classical.decPred _
  exact (Finset.mem_filter.mp (maximalWindowSet_mem object order)).2

theorem maximalWindowSet_maximal (object : FiniteObject.{u}) (order : Nat) :
    Maximal (fun windows => windows ∈ admissibleWindowSets object order)
      (maximalWindowSet object order) := by
  letI : DecidableEq (Finset (Window object order)) := Classical.decEq _
  exact (maximalWindowSelection object order).maximal

theorem maximalWindowSet_saturated (object : FiniteObject.{u}) (order : Nat)
    (window : Window object order) :
    ∃ selected ∈ maximalWindowSet object order,
      ¬ Disjoint (support object order window)
        (support object order selected) ∨
      window = selected := by
  classical
  by_cases member : window ∈ maximalWindowSet object order
  · exact ⟨window, member, Or.inr rfl⟩
  · by_contra absent
    push Not at absent
    have inserted :
        insert window (maximalWindowSet object order) ∈
          admissibleWindowSets object order := by
      have admissible := maximalWindowSet_admissible object order
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powerset.mpr
        intro item itemMem
        simp only [Finset.mem_insert] at itemMem
        rcases itemMem with rfl | itemMem
        · simp [windowSchedule]
        · have baseSubset := Finset.mem_powerset.mp
            ((Finset.mem_filter.mp (maximalWindowSet_mem object order)).1)
          exact baseSubset itemMem
      · intro left right leftMem rightMem different
        simp only [Finset.mem_insert] at leftMem rightMem
        by_cases leftNew : left = window
        · subst left
          rcases rightMem with rfl | rightMem
          · exact (different rfl).elim
          · exact (absent right rightMem).1
        · by_cases rightNew : right = window
          · subst right
            rcases leftMem with rfl | leftMem
            · exact (different rfl).elim
            · exact (absent left leftMem).1.symm
          · rcases leftMem with rfl | leftMem <;>
              rcases rightMem with rfl | rightMem
            · exact (leftNew rfl).elim
            · exact (leftNew rfl).elim
            · exact (rightNew rfl).elim
            · exact admissible leftMem rightMem different
    have maximal := maximalWindowSet_maximal object order
    have subset := maximal.2 inserted (Finset.subset_insert _ _)
    exact member (subset (Finset.mem_insert_self window _))


/-- Reusable maximal-only packing profile. -/
structure Profile (object : FiniteObject.{u}) (order : Nat) where
  selected : List (Window object order)
  selected_nodup : selected.Nodup
  pairwiseDisjoint :
    forall left, left ∈ selected -> forall right, right ∈ selected ->
      left ≠ right ->
        Disjoint (support object order left) (support object order right)
  saturated :
    forall window : Window object order,
      ∃ selectedWindow ∈ selected,
        ¬ Disjoint (support object order window)
          (support object order selectedWindow) ∨
          window = selectedWindow

/-- Canonical Graph-owned profile obtained from the framework's maximal
finite selection.  Callers never supply a selected packing or its
saturation/disjointness proofs. -/
noncomputable def maximalProfile
    (object : FiniteObject.{u}) (order : Nat) : Profile object order := by
  classical
  let selected := maximalWindowSet object order
  exact {
    selected := selected.toList
    selected_nodup := selected.nodup_toList
    pairwiseDisjoint := by
      intro left leftMem right rightMem different
      exact maximalWindowSet_admissible object order
        (Finset.mem_toList.mp leftMem) (Finset.mem_toList.mp rightMem)
        different
    saturated := by
      intro window
      obtain ⟨chosen, chosenMem, relation⟩ :=
        maximalWindowSet_saturated object order window
      exact ⟨chosen, Finset.mem_toList.mpr chosenMem, relation⟩
  }


def conflict (object : FiniteObject.{u}) (order : Nat)
    (left right : Window object order) : Prop :=
  ¬ Disjoint (support object order left) (support object order right)

noncomputable def Profile.toCore (profile : Profile object order) :
    @Core.Finite.MaximalSelection.Profile _
      (@Core.Finite.Enumeration.ofNodupList _ (Classical.decEq _)
        profile.selected profile.selected_nodup)
      (conflict object order) (Classical.decRel _) := by
  letI : DecidableRel (conflict object order) := Classical.decRel _
  exact {
    selected := profile.selected
    selected_nodup := profile.selected_nodup
    pairwiseCompatible := by
      intro left right leftMem rightMem different conflict
      exact conflict (profile.pairwiseDisjoint left leftMem right rightMem different)
    maximal := by
      intro item itemMem
      rcases profile.saturated item with ⟨selectedItem, selectedMem, conflictItem⟩
      exact ⟨selectedItem, selectedMem, conflictItem⟩ }

namespace Profile

variable {object : FiniteObject.{u}} {order : Nat}
variable (profile : Profile object order)

def packingNumber : Nat :=
  profile.selected.length

def workBudget : _root_.Hypostructure.Core.PolynomialCheckBudget Unit :=
  _root_.Hypostructure.Core.PolynomialCheckBudget.constant
    (fun _ => profile.packingNumber) profile.packingNumber

structure VerifiedStage : Type u where
  selected : List (Window object order)
  selected_eq : selected = profile.selected
  saturated : forall window : Window object order,
    ∃ selectedWindow ∈ profile.selected,
      ¬ Disjoint (support object order window)
        (support object order selectedWindow) ∨
      window = selectedWindow
  pairwiseDisjoint :
    forall left, left ∈ profile.selected -> forall right, right ∈ profile.selected ->
      left ≠ right ->
        Disjoint (support object order left) (support object order right)
  work : profile.workBudget.checks () = profile.packingNumber

def verifiedStage : profile.VerifiedStage where
  selected := profile.selected
  selected_eq := rfl
  saturated := profile.saturated
  pairwiseDisjoint := profile.pairwiseDisjoint
  work := rfl

/-- Framework-owned counted execution of a certified maximal packing.  The
selected family remains a primitive of the graph contract; Core owns the
ledger-facing stage and the work accounting. -/
def execute (profile : Profile object order) : profile.VerifiedStage :=
  profile.verifiedStage

@[simp] theorem execute_selected (profile : Profile object order) :
    (profile.execute).selected = profile.selected := rfl

@[simp] theorem execute_checks (profile : Profile object order) :
    profile.workBudget.checks () = profile.packingNumber := rfl

theorem nonempty_of_realization (realization : Window object order)
    (_positive : 0 < order) :
    profile.selected ≠ [] := by
  intro empty
  rcases profile.saturated realization with ⟨selectedWindow, member, _⟩
  simp [empty] at member

end Profile

end Hypostructure.Graph.InducedPathMaximalPacking

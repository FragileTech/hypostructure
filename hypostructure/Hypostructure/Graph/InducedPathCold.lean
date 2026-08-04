import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Finite.ScheduleEvents
import Hypostructure.Core.Finite.ColdCorridor
import Hypostructure.Core.SequentialExtensionLedger
import Hypostructure.CT7.Automation
import Hypostructure.Graph.FinitePathSelection
import Hypostructure.Graph.InducedPathWindowLedger
import Hypostructure.Graph.BoundariedAtom
import Hypostructure.Graph.Response
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.Strategy.InterfaceReplacement

/-!
# Generic induced-path incidence and corridor contracts

This module owns the data shaping used by cold induced-path branches.  The
path order, regularity baseline, transit prefix, target predicate, and local
event semantics remain contract parameters.  No theorem-specific path order
or numerical budget is built into the graph layer.
-/

namespace Hypostructure.Graph.InducedPathCold

open Hypostructure.Core.Finite
open Hypostructure.Graph.InducedPathMaximalPacking
open Hypostructure.Core.SequentialExtensionLedger

universe u v w uItem uState

abbrev Window (object : FiniteObject.{u}) (order : Nat) :=
  InducedPathMaximalPacking.Window object order

def support {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact InducedPathMaximalPacking.support object order window

def externalNeighbors {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) : Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.vertexFinset.filter (fun vertex =>
    object.graph.Adj (window position) vertex) \ support window

theorem externalNeighbors_mem_iff {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) (vertex : object.Vertex) :
    vertex ∈ externalNeighbors window position ↔
      object.graph.Adj (window position) vertex ∧ vertex ∉ support window := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simp [externalNeighbors]

/-! The two parts of a window's incidence are derived from the literal graph:
internal neighbours are exactly the image of path neighbours, while external
neighbours are the ambient neighbours outside the window support. -/
def pathAdjDecide {order : Nat} (left right : Fin order) :
    Decidable ((SimpleGraph.pathGraph order).Adj left right) :=
  decidable_of_iff (left.val + 1 = right.val ∨ right.val + 1 = left.val)
    (SimpleGraph.pathGraph_adj).symm

def pathNeighborFinset (order : Nat) (position : Fin order) : Finset (Fin order) :=
  @Finset.filter (Fin order) (fun other =>
    (SimpleGraph.pathGraph order).Adj position other)
    (fun other => pathAdjDecide position other) Finset.univ

@[simp] theorem pathNeighborFinset_card_p13 (position : Fin 13) :
    (pathNeighborFinset 13 position).card =
      InducedPathWindowLedger.pathDegree 13 position := by
  fin_cases position <;> native_decide

noncomputable def internalNeighbors {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) : Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact (pathNeighborFinset order position).image window

theorem internalNeighbors_card_p13
    {object : FiniteObject.{u}} (window : Window object 13)
    (position : Fin 13) :
    (internalNeighbors window position).card =
      InducedPathWindowLedger.pathDegree 13 position := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [internalNeighbors]
  rw [Finset.card_image_iff.mpr]
  · exact pathNeighborFinset_card_p13 position
  · intro left _ right _ equality
    exact window.injective equality

theorem internalNeighbors_subset_support {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) :
    internalNeighbors window position ⊆ support window := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro vertex member
  rcases Finset.mem_image.mp member with ⟨other, _, rfl⟩
  exact Finset.mem_image.mpr ⟨other, Finset.mem_univ _, rfl⟩

theorem internalNeighbors_mem_of_support_adj
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order)
    {vertex : object.Vertex} (vertex_mem : vertex ∈ support window)
    (adjacent : object.graph.Adj (window position) vertex) :
    vertex ∈ internalNeighbors window position := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  rcases Finset.mem_image.mp vertex_mem with ⟨other, _, equality⟩
  apply Finset.mem_image.mpr
  refine ⟨other, ?_, equality⟩
  simpa [pathNeighborFinset] using
    (window.map_rel_iff).mp (equality ▸ adjacent)

theorem externalNeighbors_disjoint_internalNeighbors
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) :
    Disjoint (externalNeighbors window position)
      (internalNeighbors window position) := by
  apply Finset.disjoint_left.mpr
  intro vertex external_mem internal_mem
  exact (externalNeighbors_mem_iff window position vertex).mp external_mem |>.2
    ((internalNeighbors_subset_support window position) internal_mem)

theorem ambientNeighbor_mem_external_or_internal
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order)
    {vertex : object.Vertex} (adjacent : object.graph.Adj (window position) vertex) :
    vertex ∈ externalNeighbors window position ∨
      vertex ∈ internalNeighbors window position := by
  by_cases in_support : vertex ∈ support window
  · exact Or.inr (internalNeighbors_mem_of_support_adj window position
      in_support adjacent)
  · exact Or.inl ((externalNeighbors_mem_iff window position vertex).mpr
      ⟨adjacent, in_support⟩)

noncomputable def ambientNeighborFinset {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) : Finset object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  exact object.graph.neighborFinset (window position)

noncomputable def externalInternalUnion {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact externalNeighbors window position ∪ internalNeighbors window position

theorem externalInternalUnion_eq_ambientNeighbors
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) :
    externalInternalUnion window position = ambientNeighborFinset window position := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  ext vertex
  constructor
  · intro member
    rcases Finset.mem_union.mp member with external | internal
    · simpa [ambientNeighborFinset] using
        (externalNeighbors_mem_iff window position vertex).mp external |>.1
    · rcases Finset.mem_image.mp internal with ⟨other, _, equality⟩
      change vertex ∈ object.graph.neighborFinset (window position)
      rw [← equality]
      simpa only [SimpleGraph.mem_neighborFinset] using
        (window.map_rel_iff).mpr (by
          simpa [pathNeighborFinset] using
            (show other ∈ pathNeighborFinset order position from by
              simpa [internalNeighbors] using ‹other ∈ pathNeighborFinset order position›))
  · intro member
    have adjacent : object.graph.Adj (window position) vertex := by
      simpa [ambientNeighborFinset] using member
    rcases ambientNeighbor_mem_external_or_internal window position adjacent with
      external | internal
    · exact Finset.mem_union.mpr (Or.inl external)
    · exact Finset.mem_union.mpr (Or.inr internal)

theorem externalNeighbors_card_add_internalNeighbors_card
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (position : Fin order) :
    (externalNeighbors window position).card +
        (internalNeighbors window position).card =
      object.degree (window position) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have card_union := Finset.card_union_of_disjoint
    (externalNeighbors_disjoint_internalNeighbors window position)
  have unionEq : externalNeighbors window position ∪
      internalNeighbors window position = ambientNeighborFinset window position := by
    simpa [externalInternalUnion] using
      externalInternalUnion_eq_ambientNeighbors window position
  rw [unionEq] at card_union
  rw [← card_union]
  change (object.graph.neighborFinset (window position)).card =
    object.graph.degree (window position)
  exact SimpleGraph.card_neighborFinset_eq_degree _ _

def externalStubCount {object : FiniteObject.{u}}
    {order : Nat} (window : Window object order) : Nat :=
  ∑ position : Fin order, (externalNeighbors window position).card

noncomputable def internalStubCount {object : FiniteObject.{u}}
    {order : Nat} (window : Window object order) : Nat :=
  ∑ position : Fin order, (internalNeighbors window position).card

/-- Domain-independent degree-sum identity for an induced-path block.  Both
the path order and the baseline are parameters; no window constant is stored. -/
theorem externalStubCount_add_internalStubCount_eq
    {object : FiniteObject.{u}} {order baseline : Nat}
    (window : Window object order)
    (minimumDegree : baseline ≤ object.minDegree) :
    externalStubCount window + internalStubCount window =
      baseline * order +
        InducedPathWindowLedger.singleWindowSurplus baseline window := by
  have degreeLower : ∀ position : Fin order,
      baseline ≤ object.degree (window position) := fun position =>
    minimumDegree.trans (object.minDegree_le_degree (window position))
  calc
    externalStubCount window + internalStubCount window =
        ∑ position : Fin order,
          ((externalNeighbors window position).card +
            (internalNeighbors window position).card) := by
          simp [externalStubCount, internalStubCount, Finset.sum_add_distrib]
    _ = ∑ position : Fin order, object.degree (window position) := by
          apply Finset.sum_congr rfl
          intro position _
          exact externalNeighbors_card_add_internalNeighbors_card window position
    _ = ∑ position : Fin order,
          (baseline + (object.degree (window position) - baseline)) := by
          apply Finset.sum_congr rfl
          intro position _
          have lower := degreeLower position
          omega
    _ = baseline * order +
        InducedPathWindowLedger.singleWindowSurplus baseline window := by
          rw [Finset.sum_add_distrib,
            InducedPathWindowLedger.singleWindowSurplus_eq_sum]
          simp [Nat.mul_comm]

/-- Exact additive external-incidence account for an induced-path block.

The internal incidence identity is an input theorem about the block family,
not a numeric constant.  In a strategy it is read from the registered exact
finite block table.  Keeping the conclusion additive avoids truncated
subtraction and exposes the coefficient derived from `baseline` and `order`. -/
theorem externalStubCount_add_twice_pred_eq
    {object : FiniteObject.{u}} {order baseline : Nat}
    (window : Window object order)
    (minimumDegree : baseline ≤ object.minDegree)
    (internalExact : internalStubCount window = 2 * (order - 1)) :
    externalStubCount window + 2 * (order - 1) =
      baseline * order +
        InducedPathWindowLedger.singleWindowSurplus baseline window := by
  rw [← internalExact]
  exact externalStubCount_add_internalStubCount_eq window minimumDegree

/-- Sum the exact additive account over an arbitrary duplicate-free block
schedule.  Every quantity is evaluated from that schedule; no path order,
baseline, block count, or external-stub coefficient is stored here. -/
theorem sum_externalStubCount_add_internalBaseline_eq
    {object : FiniteObject.{u}} {order baseline : Nat}
    (windows : Core.Finite.Enumeration (Window object order))
    (minimumDegree : baseline ≤ object.minDegree)
    (internalExact : ∀ window ∈ windows.values,
      internalStubCount window = 2 * (order - 1)) :
    (windows.values.map externalStubCount).sum +
        (2 * (order - 1)) * windows.card =
      (baseline * order) * windows.card +
        (windows.values.map
          (InducedPathWindowLedger.singleWindowSurplus baseline)).sum := by
  rw [Core.Finite.Enumeration.card]
  calc
    (windows.values.map externalStubCount).sum +
          (2 * (order - 1)) * windows.values.length =
        (windows.values.map fun window =>
          externalStubCount window + 2 * (order - 1)).sum := by
            simp [List.sum_map_add, Nat.mul_comm]
    _ = (windows.values.map fun window =>
          baseline * order +
            InducedPathWindowLedger.singleWindowSurplus baseline window).sum := by
            exact congrArg List.sum (List.map_congr_left fun window member =>
              externalStubCount_add_twice_pred_eq window minimumDegree
                (internalExact window member))
    _ = (baseline * order) * windows.values.length +
          (windows.values.map
            (InducedPathWindowLedger.singleWindowSurplus baseline)).sum := by
            rw [List.sum_map_add]
            change (List.map (Function.const _ (baseline * order))
              windows.values).sum + _ = _
            simp [List.map_const, Nat.mul_comm]

theorem externalStubCount_p13_of_cubic
    {object : FiniteObject.{u}} (window : Window object 13)
    (cubic : ∀ position : Fin 13, object.degree (window position) = 3) :
    externalStubCount window = 15 := by
  have perPosition : ∀ position : Fin 13,
      (externalNeighbors window position).card =
        3 - InducedPathWindowLedger.pathDegree 13 position := by
    intro position
    have incidence := externalNeighbors_card_add_internalNeighbors_card
      window position
    rw [internalNeighbors_card_p13 window position, cubic position] at incidence
    omega
  unfold externalStubCount
  simp_rw [perPosition]
  native_decide

theorem externalStubCount_p13_of_minDegree
    {object : FiniteObject.{u}} (window : Window object 13)
    (minimumDegree : 3 ≤ object.minDegree) :
    15 ≤ externalStubCount window := by
  have perPosition : ∀ position : Fin 13,
      3 - InducedPathWindowLedger.pathDegree 13 position ≤
        (externalNeighbors window position).card := by
    intro position
    have incidence := externalNeighbors_card_add_internalNeighbors_card
      window position
    rw [internalNeighbors_card_p13 window position] at incidence
    have degreeLower : 3 ≤ object.degree (window position) :=
      minimumDegree.trans (object.minDegree_le_degree (window position))
    omega
  calc
    15 = ∑ position : Fin 13,
        (3 - InducedPathWindowLedger.pathDegree 13 position) := by
          native_decide
    _ ≤ ∑ position : Fin 13,
        (externalNeighbors window position).card := by
          exact Finset.sum_le_sum fun position _ => perPosition position
    _ = externalStubCount window := rfl

/-- `lem:exact-window-join-identity`.  The external stub count of a packed
`P₁₃` window in a minimum-degree-three graph is *exactly* fifteen plus the
window's own surplus above the cubic baseline -- the same per-window summand
`InducedPathWindowLedger.windowSurplus` aggregates.

Every ambient neighbour of a window vertex is either internal, and then it is
one of the `pathDegree` path neighbours
(`internalNeighbors_card_p13`), or external
(`externalNeighbors_card_add_internalNeighbors_card`).  So position by
position the external count is `d(v) - pathDegree`, which splits as
`(3 - pathDegree) + (d(v) - 3)` because `pathDegree ≤ 2 ≤ 3 ≤ d(v)`.  Summing
the first part over the thirteen positions gives the fifteen cubic stubs and
summing the second gives the window surplus.

This is the exact (and therefore also upper) form of
`externalStubCount_p13_of_minDegree`, which only bounds the count from below,
and it needs no ambient-cubic hypothesis, unlike
`externalStubCount_p13_of_cubic`. -/
theorem externalStubCount_p13_eq_add_windowSurplus
    {object : FiniteObject.{u}} (window : Window object 13)
    (minimumDegree : 3 ≤ object.minDegree) :
    externalStubCount window =
      15 + InducedPathWindowLedger.singleWindowSurplus 3 window := by
  have perPosition : ∀ position : Fin 13,
      (externalNeighbors window position).card =
        (3 - InducedPathWindowLedger.pathDegree 13 position) +
          (object.degree (window position) - 3) := by
    intro position
    have incidence := externalNeighbors_card_add_internalNeighbors_card
      window position
    rw [internalNeighbors_card_p13 window position] at incidence
    have degreeLower : 3 ≤ object.degree (window position) :=
      minimumDegree.trans (object.minDegree_le_degree (window position))
    have pathUpper : InducedPathWindowLedger.pathDegree 13 position ≤ 2 := by
      unfold InducedPathWindowLedger.pathDegree
      split <;> omega
    omega
  have cubicStubs : ∑ position : Fin 13,
      (3 - InducedPathWindowLedger.pathDegree 13 position) = 15 := by
    simp [Fin.sum_univ_succ, InducedPathWindowLedger.pathDegree]
  calc
    externalStubCount window
        = ∑ position : Fin 13,
          ((3 - InducedPathWindowLedger.pathDegree 13 position) +
            (object.degree (window position) - 3)) := by
          unfold externalStubCount
          exact Finset.sum_congr rfl fun position _ => perPosition position
    _ = (∑ position : Fin 13,
            (3 - InducedPathWindowLedger.pathDegree 13 position)) +
          ∑ position : Fin 13, (object.degree (window position) - 3) :=
          Finset.sum_add_distrib
    _ = 15 + InducedPathWindowLedger.singleWindowSurplus 3 window := by
          rw [cubicStubs, InducedPathWindowLedger.singleWindowSurplus_eq_sum]

private theorem sum_map_const_add {Item : Type w} (items : List Item)
    (constant : Nat) (value : Item → Nat) :
    (items.map fun item => constant + value item).sum =
      constant * items.length + (items.map value).sum := by
  induction items with
  | nil => simp
  | cons item tail ih =>
      have expand :
          constant * (tail.length + 1) = constant * tail.length + constant :=
        Nat.mul_succ constant tail.length
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, expand]
      omega

theorem externalStubSum_p13_eq_add_windowSurplus
    {object : FiniteObject.{u}}
    (profile : InducedPathMaximalPacking.Profile object 13)
    (minimumDegree : 3 ≤ object.minDegree) :
    ((InducedPathWindowLedger.windowIndices profile).map fun index =>
        externalStubCount
          (InducedPathWindowLedger.selectedWindow index)).sum =
      15 * profile.selected.length +
        InducedPathWindowLedger.windowSurplus object 13 3 profile := by
  have perWindow :
      (fun index : InducedPathWindowLedger.WindowIndex object 13 profile =>
          externalStubCount (InducedPathWindowLedger.selectedWindow index)) =
        fun index : InducedPathWindowLedger.WindowIndex object 13 profile =>
          15 +
            InducedPathWindowLedger.singleWindowSurplus 3
              (InducedPathWindowLedger.selectedWindow index) :=
    funext fun index =>
      externalStubCount_p13_eq_add_windowSurplus
        (InducedPathWindowLedger.selectedWindow index) minimumDegree
  have aggregate :
      ((InducedPathWindowLedger.windowIndices profile).map fun index =>
          15 +
            InducedPathWindowLedger.singleWindowSurplus 3
              (InducedPathWindowLedger.selectedWindow index)).sum =
        15 * (InducedPathWindowLedger.windowIndices profile).length +
          ((InducedPathWindowLedger.windowIndices profile).map fun index =>
            InducedPathWindowLedger.singleWindowSurplus 3
              (InducedPathWindowLedger.selectedWindow index)).sum :=
    sum_map_const_add _ _ _
  rw [perWindow, aggregate, InducedPathWindowLedger.windowIndices_length,
    InducedPathWindowLedger.windowSurplus_eq_sum_singleWindowSurplus]

abbrev Token (object : FiniteObject.{u}) (order : Nat)
    (window : Window object order) :=
  Sigma fun position : Fin order =>
    {vertex : object.Vertex // vertex ∈ externalNeighbors window position}

noncomputable def tokenSchedule {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) : Enumeration (Token object order window) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : FinEnum (Token object order window) := inferInstance
  letI : DecidableEq (Token object order window) := inferInstance
  exact Enumeration.ofFinEnum (inferInstance : FinEnum (Token object order window))

@[simp] theorem mem_tokenSchedule_values
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (token : Token object order window) :
    token ∈ (tokenSchedule window).values := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : FinEnum (Token object order window) := inferInstance
  exact Enumeration.mem_ofFinEnum_values inferInstance token

@[simp] theorem tokenSchedule_card {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) :
    (tokenSchedule window).card =
      ∑ position : Fin order, (externalNeighbors window position).card := by
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : FinEnum (Token object order window) := inferInstance
  change (Enumeration.ofFinEnum
      (inferInstance : FinEnum (Token object order window))).card = _
  rw [Enumeration.card_ofFinEnum, FinEnum.card_eq_fintypeCard]
  simp [Token, Fintype.card_sigma]

noncomputable def branchExcess {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (transit : Nat) :
    List (Token object order window) :=
  (tokenSchedule window).values.drop transit

theorem branchExcess_length {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (transit : Nat)
    (_transit_le : transit ≤ (tokenSchedule window).card) :
    (branchExcess window transit).length =
      (tokenSchedule window).card - transit := by
  simp [branchExcess, Enumeration.card]

theorem branchExcess_length_p13_of_cubic
    {object : FiniteObject.{u}} (window : Window object 13)
    (cubic : ∀ position : Fin 13, object.degree (window position) = 3) :
    (branchExcess window 2).length = 13 := by
  have stubs : (tokenSchedule window).card = 15 := by
    rw [tokenSchedule_card]
    exact externalStubCount_p13_of_cubic window cubic
  rw [branchExcess_length window 2]
  · omega
  · omega

/-- Removing the two transit stubs from a minimum-degree-three `P₁₃`
still leaves a literal branch-excess occurrence. -/
theorem branchExcess_nonempty_p13_of_minDegree
    {object : FiniteObject.{u}} (window : Window object 13)
    (minimumDegree : 3 ≤ object.minDegree) :
    branchExcess window 2 ≠ [] := by
  have stubs : 15 ≤ (tokenSchedule window).card := by
    rw [tokenSchedule_card]
    exact externalStubCount_p13_of_minDegree window minimumDegree
  have transit : 2 ≤ (tokenSchedule window).card := by omega
  have lengthEq := branchExcess_length window 2 transit
  intro empty
  have lengthZero : (branchExcess window 2).length = 0 := by simp [empty]
  rw [lengthEq] at lengthZero
  omega

theorem branchExcess_nodup {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (transit : Nat) :
    (branchExcess window transit).Nodup := by
  exact (tokenSchedule window).nodup.drop

/-! The selected branch-excess family is one literal schedule.  Its window
index is retained in each occurrence, so later ledger consumers can recover
the owning packed window without rebuilding a support or consulting a
second list. -/
abbrev BranchExcessOccurrence (object : FiniteObject.{u}) (order : Nat) :=
  Σ window : Window object order, Token object order window

noncomputable def selectedBranchExcess
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    List (BranchExcessOccurrence object order) :=
  profile.selected.flatMap fun window =>
    (branchExcess window 2).map fun token => ⟨window, token⟩

theorem selectedBranchExcess_nodup
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    (selectedBranchExcess profile).Nodup := by
  classical
  apply List.nodup_flatMap.mpr
  constructor
  · intro window _member
    exact (branchExcess_nodup window 2).map (by
      intro left right equality
      cases equality
      rfl)
  · have pairwise_of_nodup : ∀ (windows : List (Window object order)),
        windows.Nodup →
            List.Pairwise
            (Function.onFun List.Disjoint fun window =>
              (branchExcess window 2).map fun token =>
                (⟨window, token⟩ : BranchExcessOccurrence object order))
            windows := by
      intro windows windows_nodup
      induction windows with
      | nil => simp
      | cons head tail ih =>
          have head_not_mem : head ∉ tail :=
            (List.nodup_cons.mp windows_nodup).1
          have tail_nodup : tail.Nodup :=
            (List.nodup_cons.mp windows_nodup).2
          simp only [List.pairwise_cons]
          constructor
          · intro other other_mem
            apply List.disjoint_left.mpr
            intro occurrence head_occurrence other_occurrence
            rcases List.mem_map.mp head_occurrence with
              ⟨head_token, _, head_eq⟩
            rcases List.mem_map.mp other_occurrence with
              ⟨other_token, _, other_eq⟩
            have sigma_eq :
                (⟨head, head_token⟩ : BranchExcessOccurrence object order) =
                  ⟨other, other_token⟩ := head_eq.trans other_eq.symm
            have window_eq : head = other := congrArg Sigma.fst sigma_eq
            exact head_not_mem (window_eq ▸ other_mem)
          · exact ih tail_nodup
    exact pairwise_of_nodup profile.selected profile.selected_nodup

theorem window_mem_of_branchExcess_mem
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (occurrence : BranchExcessOccurrence object order)
    (member : occurrence ∈ selectedBranchExcess profile) :
    occurrence.1 ∈ profile.selected := by
  unfold selectedBranchExcess at member
  rw [List.mem_flatMap] at member
  obtain ⟨window, window_mem, token_mem⟩ := member
  rcases List.mem_map.mp token_mem with ⟨token, _, equal⟩
  have : window = occurrence.1 := congrArg Sigma.fst equal
  simpa [this] using window_mem

noncomputable def selectedBranchExcessSchedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (BranchExcessOccurrence object order) := by
  classical
  exact Enumeration.ofNodupList
    (selectedBranchExcess profile) (selectedBranchExcess_nodup profile)

@[simp] theorem selectedBranchExcessSchedule_values
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    (selectedBranchExcessSchedule profile).values = selectedBranchExcess profile :=
  rfl

theorem selectedBranchExcess_length_p13_of_cubic
    {object : FiniteObject.{u}}
    (profile : InducedPathMaximalPacking.Profile object 13)
    (cubic : ∀ window ∈ profile.selected, ∀ position : Fin 13,
      object.degree (window position) = 3) :
    (selectedBranchExcess profile).length = 13 * profile.selected.length := by
  classical
  unfold selectedBranchExcess
  simp only [List.length_flatMap, List.length_map]
  have aux : ∀ (windows : List (Window object 13)),
      (∀ window ∈ windows, (branchExcess window 2).length = 13) →
      (List.map (fun window => (branchExcess window 2).length) windows).sum =
        13 * windows.length := by
    intro windows all_cubic
    induction windows with
    | nil => simp
    | cons head tail ih =>
        have head_length := all_cubic head (by simp)
        have tail_cubic : ∀ window ∈ tail,
            (branchExcess window 2).length = 13 := by
          intro window member
          exact all_cubic window (by simp [member])
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [head_length, ih tail_cubic]
        omega
  exact aux profile.selected (by
    intro window member
    exact branchExcess_length_p13_of_cubic window (cubic window member))

theorem selectedBranchExcess_nonempty_of_cubic
    {object : FiniteObject.{u}}
    (profile : InducedPathMaximalPacking.Profile object 13)
    (cubic : ∀ window ∈ profile.selected, ∀ position : Fin 13,
      object.degree (window position) = 3)
    (selected_nonempty : profile.selected ≠ []) :
    selectedBranchExcess profile ≠ [] := by
  intro empty
  have length_zero : (selectedBranchExcess profile).length = 0 := by
    simp [empty]
  rw [selectedBranchExcess_length_p13_of_cubic profile cubic] at length_zero
  have selected_length_ne : profile.selected.length ≠ 0 := by
    intro length_zero
    exact selected_nonempty (List.length_eq_zero_iff.mp length_zero)
  have selected_length_pos : 0 < profile.selected.length :=
    Nat.pos_of_ne_zero selected_length_ne
  omega

/-- Framework-ready nonemptiness of the complete owner-tagged branch-excess
schedule.  The selected packing and the graph minimum degree are the only
inputs; no cold-window list or witness is supplied by an application. -/
theorem selectedBranchExcess_nonempty_of_minDegree
    {object : FiniteObject.{u}}
    (profile : InducedPathMaximalPacking.Profile object 13)
    (minimumDegree : 3 ≤ object.minDegree)
    (selected_nonempty : profile.selected ≠ []) :
    selectedBranchExcess profile ≠ [] := by
  obtain ⟨window, window_mem⟩ :=
    List.exists_mem_of_ne_nil profile.selected selected_nonempty
  obtain ⟨token, token_mem⟩ := List.exists_mem_of_ne_nil
    (branchExcess window 2)
    (branchExcess_nonempty_p13_of_minDegree window minimumDegree)
  apply List.ne_nil_of_mem
  rw [selectedBranchExcess, List.mem_flatMap]
  exact ⟨window, window_mem,
    List.mem_map.mpr ⟨token, token_mem, rfl⟩⟩

theorem selectedBranchExcessSchedule_nonempty_of_minDegree
    {object : FiniteObject.{u}}
    (profile : InducedPathMaximalPacking.Profile object 13)
    (minimumDegree : 3 ≤ object.minDegree)
    (selected_nonempty : profile.selected ≠ []) :
    (selectedBranchExcessSchedule profile).values ≠ [] := by
  simpa only [selectedBranchExcessSchedule_values] using
    selectedBranchExcess_nonempty_of_minDegree profile minimumDegree
      selected_nonempty

/-! Core's overlap accounting is applied to the literal branch-excess
occurrence schedule.  Occurrences retain their owning window, so the support
map is derived from that owner and no second incidence list is introduced. -/
noncomputable def selectedBranchExcessOverlapBound
    {object : FiniteObject.{u}}
    (profile : InducedPathMaximalPacking.Profile object 13) : Nat :=
  Core.Finite.ColdCorridor.overlapBound
    (selectedBranchExcessSchedule profile)
    (Enumeration.ofFinEnum object.vertices)
    (fun occurrence => support occurrence.1)

theorem selectedBranchExcessOverlapCount_le_bound
    {object : FiniteObject.{u}}
    (profile : InducedPathMaximalPacking.Profile object 13)
    (vertex : object.Vertex) :
    Core.Finite.ColdCorridor.overlapCount
      (selectedBranchExcessSchedule profile)
      (fun occurrence => support occurrence.1) vertex ≤
      selectedBranchExcessOverlapBound profile := by
  apply Core.Finite.ColdCorridor.overlapCount_le_bound
    (selectedBranchExcessSchedule profile)
    (Enumeration.ofFinEnum object.vertices)
    (fun occurrence => support occurrence.1) vertex
  exact object.mem_vertexFinset vertex

structure Regularity (object : FiniteObject.{u}) (order baseline : Nat)
    (window : Window object order) where
  degree_eq : ∀ position : Fin order, object.degree (window position) = baseline

noncomputable def regularityDecidable {object : FiniteObject.{u}} {order baseline : Nat}
    (window : Window object order) : Decidable (Regularity object order baseline window) := by
  exact Classical.propDecidable _

noncomputable def branchExcessChecks {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) : Nat :=
  (tokenSchedule window).card

theorem branchExcessChecks_linear {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) :
  branchExcessChecks window ≤ (tokenSchedule window).card := le_rfl

/-! The surviving cold support is projected from the existing sequential
ledger.  Core's filtration supplies both the exact rejected list and its
duplicate-free proof; this adapter only turns that literal list into the
standard Enumeration consumed by later CT schedules. -/
noncomputable def coldSupportSchedule
    {profile : Core.SequentialExtensionLedger.Profile.{u, u}}
    {aggregate : profile.Aggregate} {windows : List profile.Window}
    (ledger : Core.SequentialExtensionLedger.Ledger profile aggregate windows)
    (windows_nodup : windows.Nodup) : Enumeration profile.Window :=
  by
    classical
    exact Enumeration.ofNodupList ledger.cold
      (Core.SequentialExtensionLedger.Ledger.cold_nodup ledger windows_nodup)

@[simp] theorem coldSupportSchedule_values
    {profile : Core.SequentialExtensionLedger.Profile.{u, u}}
    {aggregate : profile.Aggregate} {windows : List profile.Window}
    (ledger : Core.SequentialExtensionLedger.Ledger profile aggregate windows)
    (windows_nodup : windows.Nodup) :
    (coldSupportSchedule ledger windows_nodup).values = ledger.cold :=
  by rfl

/-! The exact overlap constant for a selected induced-path family is computed
by Core's finite support accounting. -/
noncomputable def selectedWindowSchedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (Window object order) := by
  classical
  exact Enumeration.ofNodupList profile.selected profile.selected_nodup

noncomputable def selectedWindowOverlapBound
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) : Nat :=
  Core.Finite.ColdCorridor.overlapBound
    (selectedWindowSchedule profile)
    (Enumeration.ofFinEnum object.vertices)
    (support (object := object) (order := order))

theorem selectedWindowOverlapCount_le_bound
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (vertex : object.Vertex) :
    Core.Finite.ColdCorridor.overlapCount
      (selectedWindowSchedule profile) (support (object := object) (order := order)) vertex ≤
      selectedWindowOverlapBound profile := by
  apply Core.Finite.ColdCorridor.overlapCount_le_bound
    (selectedWindowSchedule profile)
    (Enumeration.ofFinEnum object.vertices)
    (support (object := object) (order := order)) vertex
  exact object.mem_vertexFinset vertex

/-! ## Graph-derived cold exterior

The cold exterior is computed from the selected packing itself.  All
subsequent schedules are restrictions of Core enumerations, so no application
can provide a second support, stub family, or component assignment. -/

noncomputable def selectedSupport
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Finset object.Vertex := by
  classical
  exact profile.selected.toFinset.biUnion
    (support (object := object) (order := order))

theorem mem_selectedSupport_iff
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (vertex : object.Vertex) :
    vertex ∈ selectedSupport profile ↔
      ∃ window ∈ profile.selected, vertex ∈ support window := by
  classical
  simp [selectedSupport]

/-! `def:cold-corridor-first-failure` deletes *the interiors* of the cold
windows, not the windows: "Delete the interiors of these windows and look at a
connected component `K` of the remaining outside graph.  The boundary stubs of
`K` are the edges from `K` to ambient-cubic cold windows."  A window is an
induced path of the registered `order`, so its two ends are the positions `0`
and `order - 1` and its interior is every other position.  The two ends survive
the deletion and remain available as endpoints of boundary stubs, which is what
gives *every* selected branch-excess half-edge a corridor. -/
def interiorPositions (order : Nat) : Finset (Fin order) :=
  Finset.univ.filter fun position =>
    position.val ≠ 0 ∧ position.val + 1 ≠ order

@[simp] theorem mem_interiorPositions_iff {order : Nat} (position : Fin order) :
    position ∈ interiorPositions order ↔
      position.val ≠ 0 ∧ position.val + 1 ≠ order := by
  simp [interiorPositions]

/-- The interior of one window: the image of the positions strictly between the
two ends of the induced path.  This is the part `def:cold-corridor-first-failure`
deletes. -/
noncomputable def windowInterior
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (interiorPositions order).image window

theorem windowInterior_subset_support
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) :
    windowInterior window ⊆ support window := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro vertex member
  rcases Finset.mem_image.mp member with ⟨position, _, rfl⟩
  exact Finset.mem_image.mpr ⟨position, Finset.mem_univ _, rfl⟩

noncomputable def selectedInterior
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Finset object.Vertex := by
  classical
  exact profile.selected.toFinset.biUnion
    (windowInterior (object := object) (order := order))

theorem mem_selectedInterior_iff
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (vertex : object.Vertex) :
    vertex ∈ selectedInterior profile ↔
      ∃ window ∈ profile.selected, vertex ∈ windowInterior window := by
  classical
  simp [selectedInterior]

theorem selectedInterior_subset_selectedSupport
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    selectedInterior profile ⊆ selectedSupport profile := by
  classical
  intro vertex member
  obtain ⟨window, windowMember, vertexMember⟩ :=
    (mem_selectedInterior_iff profile vertex).mp member
  exact (mem_selectedSupport_iff profile vertex).mpr
    ⟨window, windowMember, windowInterior_subset_support window vertexMember⟩

noncomputable def exteriorSupport
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact object.vertexFinset \ selectedInterior profile

theorem mem_exteriorSupport_iff
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (vertex : object.Vertex) :
    vertex ∈ exteriorSupport profile ↔ vertex ∉ selectedInterior profile := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  constructor
  · intro member
    exact (Finset.mem_sdiff.mp member).2
  · intro absent
    exact Finset.mem_sdiff.mpr ⟨object.mem_vertexFinset vertex, absent⟩

/-- Both ends of every selected window survive the deletion: they are boundary
vertices, not interior ones, so they stay in the outside graph and can carry
boundary stubs. -/
theorem window_end_mem_exteriorSupport
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    {window : Window object order} (windowMember : window ∈ profile.selected)
    (position : Fin order)
    (isEnd : position.val = 0 ∨ position.val + 1 = order) :
    window position ∈ exteriorSupport profile := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  refine (mem_exteriorSupport_iff profile _).mpr ?_
  intro member
  obtain ⟨other, otherMember, interiorMember⟩ :=
    (mem_selectedInterior_iff profile _).mp member
  have ownSupport : window position ∈ support window :=
    Finset.mem_image.mpr ⟨position, Finset.mem_univ _, rfl⟩
  by_cases same : other = window
  · subst same
    rcases Finset.mem_image.mp interiorMember with
      ⟨otherPosition, positionMem, equal⟩
    have positionEq : otherPosition = position := other.injective equal
    have interiorFacts := (mem_interiorPositions_iff otherPosition).mp positionMem
    rw [positionEq] at interiorFacts
    rcases isEnd with zero | last
    · exact interiorFacts.1 zero
    · exact interiorFacts.2 last
  · exact Finset.disjoint_left.mp
      (profile.pairwiseDisjoint other otherMember window windowMember same)
      (windowInterior_subset_support other interiorMember) ownSupport

def tokenEndpoint
    {object : FiniteObject.{u}} {order : Nat}
    {window : Window object order} (token : Token object order window) :
    object.Vertex :=
  token.2.1

def occurrenceEndpoint
    {object : FiniteObject.{u}} {order : Nat}
    (occurrence : BranchExcessOccurrence object order) : object.Vertex :=
  tokenEndpoint occurrence.2

/-! Every external stub of every selected window, retaining its owner and
path offset.  The dependent flattening is the Core operation already used by
the packing and CT schedule APIs. -/
abbrev StubOccurrence (object : FiniteObject.{u}) (order : Nat) :=
  Σ window : Window object order, Token object order window

noncomputable def selectedStubSchedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (StubOccurrence object order) :=
  (show DependentEnumeration (Window object order)
      (fun window => Token object order window) from
    { indices := selectedWindowSchedule profile
      fibres := tokenSchedule }).flatten

@[simp] theorem mem_selectedStubSchedule_values
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (stub : StubOccurrence object order) :
    stub ∈ (selectedStubSchedule profile).values ↔
      stub.1 ∈ profile.selected := by
  rw [selectedStubSchedule, DependentEnumeration.mem_flatten_values]
  constructor
  · exact fun member => member.1
  · intro member
    exact ⟨member, mem_tokenSchedule_values stub.1 stub.2⟩

abbrev ExteriorStub
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  {stub : StubOccurrence object order //
    tokenEndpoint stub.2 ∈ exteriorSupport profile}

noncomputable def exteriorStubSchedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (ExteriorStub profile) :=
  (selectedStubSchedule profile).subtype
    (fun stub => tokenEndpoint stub.2 ∈ exteriorSupport profile)
    (fun _ => Classical.propDecidable _)

theorem exteriorStub_endpoint_mem
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (stub : ExteriorStub profile) :
    tokenEndpoint stub.1.2 ∈ exteriorSupport profile :=
  stub.2

noncomputable def exteriorComponent
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (stub : ExteriorStub profile) :
    SupportComponents.Connected.Component object (exteriorSupport profile) :=
  SupportComponents.Connected.componentOf object (exteriorSupport profile)
    ⟨tokenEndpoint stub.1.2, stub.2⟩

/-! The component boundary schedule is a Core restriction of the literal
exterior-stub schedule.  It is therefore the unique schedule later used for
cyclic successor selection. -/
noncomputable def componentBoundarySchedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (component :
      SupportComponents.Connected.Component object (exteriorSupport profile)) :
    Enumeration {stub : ExteriorStub profile //
      exteriorComponent stub = component} :=
  (exteriorStubSchedule profile).subtype
    (fun stub => exteriorComponent stub = component)
    (fun _ => Classical.propDecidable _)

abbrev ExteriorBranchOccurrence
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  {occurrence : BranchExcessOccurrence object order //
    occurrenceEndpoint occurrence ∈ exteriorSupport profile}

noncomputable def exteriorBranchSchedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (ExteriorBranchOccurrence profile) :=
  (selectedBranchExcessSchedule profile).subtype
    (fun occurrence => occurrenceEndpoint occurrence ∈ exteriorSupport profile)
    (fun _ => Classical.propDecidable _)

noncomputable def exteriorBranchComponent
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile) :
    SupportComponents.Connected.Component object (exteriorSupport profile) :=
  SupportComponents.Connected.componentOf object (exteriorSupport profile)
    ⟨occurrenceEndpoint occurrence.1, occurrence.2⟩

def exteriorStubOfBranch
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile) : ExteriorStub profile :=
  ⟨occurrence.1, occurrence.2⟩

theorem exteriorStubOfBranch_mem
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    exteriorStubOfBranch occurrence ∈
      (exteriorStubSchedule profile).values := by
  rw [exteriorStubSchedule, Enumeration.mem_subtype_values]
  rw [mem_selectedStubSchedule_values]
  have source_mem : occurrence.1 ∈
      (selectedBranchExcessSchedule profile).values :=
    (Enumeration.mem_subtype_values
      (selectedBranchExcessSchedule profile)
      (fun occurrence => occurrenceEndpoint occurrence ∈ exteriorSupport profile)
      (fun _ => Classical.propDecidable _) occurrence).mp member
  exact window_mem_of_branchExcess_mem profile occurrence.1 source_mem

theorem exteriorStubOfBranch_component
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile) :
    exteriorComponent (exteriorStubOfBranch occurrence) =
      exteriorBranchComponent occurrence := by
  rfl

theorem exteriorStubOfBranch_mem_componentBoundary
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    (⟨exteriorStubOfBranch occurrence,
      exteriorStubOfBranch_component occurrence⟩ :
        {stub : ExteriorStub profile //
          exteriorComponent stub = exteriorBranchComponent occurrence}) ∈
      (componentBoundarySchedule profile
        (exteriorBranchComponent occurrence)).values := by
  exact (Enumeration.mem_subtype_values
    (exteriorStubSchedule profile)
    (fun stub => exteriorComponent stub = exteriorBranchComponent occurrence)
    (fun _ => Classical.propDecidable _) _).mpr
      (exteriorStubOfBranch_mem occurrence member)

/-! The cyclic successor is the generic Core schedule operation applied to
the exact component-boundary enumeration. -/
noncomputable def successorBoundaryStub
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    {stub : ExteriorStub profile //
      exteriorComponent stub = exteriorBranchComponent occurrence} := by
  let schedule := componentBoundarySchedule profile
    (exteriorBranchComponent occurrence)
  let start : {stub : ExteriorStub profile //
      exteriorComponent stub = exteriorBranchComponent occurrence} :=
    ⟨exteriorStubOfBranch occurrence,
      exteriorStubOfBranch_component occurrence⟩
  have start_mem : start ∈ schedule.values :=
    exteriorStubOfBranch_mem_componentBoundary occurrence member
  have nonempty : schedule.values ≠ [] := List.ne_nil_of_mem start_mem
  exact schedule.cyclicSuccessor nonempty start start_mem

theorem successorBoundaryStub_mem
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    successorBoundaryStub occurrence member ∈
      (componentBoundarySchedule profile
        (exteriorBranchComponent occurrence)).values := by
  let schedule := componentBoundarySchedule profile
    (exteriorBranchComponent occurrence)
  let start : {stub : ExteriorStub profile //
      exteriorComponent stub = exteriorBranchComponent occurrence} :=
    ⟨exteriorStubOfBranch occurrence,
      exteriorStubOfBranch_component occurrence⟩
  have start_mem : start ∈ schedule.values :=
    exteriorStubOfBranch_mem_componentBoundary occurrence member
  have nonempty : schedule.values ≠ [] := List.ne_nil_of_mem start_mem
  exact schedule.cyclicSuccessor_mem nonempty start start_mem

/-! The return path lives in the induced exterior graph.  Equality of the
two component labels gives reachability, and the shared finite path selector
chooses the canonical path; no path is supplied by a registration. -/

noncomputable abbrev ExteriorObject
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  object.induce (exteriorSupport profile)

noncomputable def exteriorStart
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile) :
    (ExteriorObject profile).Vertex :=
  ⟨occurrenceEndpoint occurrence.1, occurrence.2⟩

noncomputable def exteriorFinish
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    (ExteriorObject profile).Vertex :=
  ⟨tokenEndpoint (successorBoundaryStub occurrence member).1.1.2,
    (successorBoundaryStub occurrence member).1.2⟩

theorem exterior_reachable
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    (ExteriorObject profile).graph.Reachable
      (exteriorStart occurrence) (exteriorFinish occurrence member) := by
  apply SimpleGraph.ConnectedComponent.exact
  change
    SupportComponents.Connected.componentOf object (exteriorSupport profile)
        (exteriorStart occurrence) =
      SupportComponents.Connected.componentOf object (exteriorSupport profile)
        (exteriorFinish occurrence member)
  exact (successorBoundaryStub occurrence member).2.symm

noncomputable def selectedReturnPath
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    (ExteriorObject profile).graph.Path
      (exteriorStart occurrence) (exteriorFinish occurrence member) := by
  let exterior := ExteriorObject profile
  letI : FinEnum exterior.Vertex := exterior.vertices
  letI : Fintype exterior.Vertex := @FinEnum.instFintype _ exterior.vertices
  letI : DecidableEq exterior.Vertex := exterior.vertices.decEq
  letI : DecidableRel exterior.graph.Adj := exterior.decideAdj
  exact (FinitePathSelection.selectOfReachable exterior.graph
    (exterior_reachable occurrence member)).path

noncomputable abbrev ReturnStage
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :=
  Fin ((selectedReturnPath occurrence member).1.length + 1)

noncomputable def returnStageSchedule
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    Enumeration (ReturnStage occurrence member) :=
  Enumeration.ofNodupList (List.ofFn id)
    (List.nodup_ofFn_ofInjective Function.injective_id)

@[simp] theorem returnStageSchedule_values
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    (returnStageSchedule occurrence member).values = List.ofFn id := rfl

theorem returnStageSchedule_nonempty
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    (returnStageSchedule occurrence member).values ≠ [] := by
  rw [returnStageSchedule_values]
  simp

@[simp] theorem returnStageSchedule_get_val
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (index : Fin (returnStageSchedule occurrence member).card) :
    ((returnStageSchedule occurrence member).get index).1 = index.1 := by
  change ((List.ofFn (fun stage : ReturnStage occurrence member => stage)).get
    index).1 = index.1
  rw [List.get_ofFn]
  rfl

noncomputable def returnPrefix
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    (ExteriorObject profile).graph.Walk
      (exteriorStart occurrence)
      ((selectedReturnPath occurrence member).1.getVert stage.1) :=
  (selectedReturnPath occurrence member).1.take stage.1

theorem returnPrefix_isPath
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    (returnPrefix occurrence member stage).IsPath :=
  (selectedReturnPath occurrence member).2.take stage.1

noncomputable def returnPrefixSupport
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    Enumeration object.Vertex := by
  let exterior := ExteriorObject profile
  letI : DecidableEq exterior.Vertex := exterior.vertices.decEq
  let inducedSchedule : Enumeration (ExteriorObject profile).Vertex :=
    Enumeration.ofNodupList
      (returnPrefix occurrence member stage).support
      (returnPrefix_isPath occurrence member stage).support_nodup
  exact inducedSchedule.map Subtype.val Subtype.val_injective
    object.vertices.decEq

noncomputable def returnEndpoint
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) : object.Vertex :=
  ((selectedReturnPath occurrence member).1.getVert stage.1).1

def offsetDistance {order : Nat} (left right : Fin order) : Nat :=
  left.1.dist right.1

/-- The canonical path-graph segment between two displayed offsets, mapped
through the exact induced-window embedding already carried by the incoming
packing occurrence. -/
noncomputable def windowSegment
    {object : FiniteObject.{u}} {order : Nat}
    (window : Window object order) (left right : Fin order) :
    object.graph.Walk (window left) (window right) :=
  (Classical.choice
    ((SimpleGraph.pathGraph_preconnected order left right))).map window.toHom

/-- The literal F1 completion: enter the exterior through the selected stub,
follow the stored return prefix, use the selected return adjacency, and close
along the owning induced window.  No walk or certificate is supplied by a
registration. -/
noncomputable def displayedF1Completion
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) (offset : Fin order)
    (returnAdj : object.graph.Adj
      (returnEndpoint occurrence member stage) (occurrence.1.1 offset)) :
    object.graph.Walk
      (occurrence.1.1 occurrence.1.2.1)
      (occurrence.1.1 occurrence.1.2.1) := by
  have entryAdj : object.graph.Adj
      (occurrence.1.1 occurrence.1.2.1)
      (occurrenceEndpoint occurrence.1) :=
    (externalNeighbors_mem_iff occurrence.1.1 occurrence.1.2.1
      (occurrenceEndpoint occurrence.1)).mp occurrence.1.2.2.2 |>.1
  let exteriorPrefix : object.graph.Walk
      (occurrenceEndpoint occurrence.1)
      (returnEndpoint occurrence member stage) :=
    (returnPrefix occurrence member stage).map
      (object.induceEmbedding (exteriorSupport profile)).toHom
  exact SimpleGraph.Walk.cons entryAdj
    (exteriorPrefix.append
      (SimpleGraph.Walk.cons returnAdj
        (windowSegment occurrence.1.1 offset occurrence.1.2.1)))

/-- Exact semantic predicate checked by F1 on the displayed completion.  A
stored hit therefore already contains both the closing adjacency and the
cycle proof; downstream code only eliminates that ledger witness. -/
def F1Valid
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (stage : ReturnStage occurrence member) (offset : Fin order) : Prop :=
  ∃ returnAdj : object.graph.Adj
      (returnEndpoint occurrence member stage) (occurrence.1.1 offset),
    let completion := displayedF1Completion occurrence member stage offset returnAdj
    completion.IsCycle ∧ CycleLengthOK completion.length

/-! Literal F1 candidates are the displayed offsets of the owning window.
The validity predicate is exactly adjacency of the current return endpoint
and acceptance of the cycle length computed from the prefix and the two
attachment edges.  Core performs the ordered search over this family. -/
noncomputable def f1EventFamily
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK) :
    Core.Finite.ColdCorridor.EventFamily
      (ReturnStage occurrence member)
      (fun _ => object.Vertex) (fun _ => ULift.{u} (Fin order)) where
  schedule := fun _ =>
    (Enumeration.ofFinEnum (inferInstance : FinEnum (Fin order))).map
      ULift.up ULift.up_injective (Classical.decEq _)
  valid := fun stage offset _endpoint =>
    F1Valid occurrence member CycleLengthOK stage offset.down
  valid_decidable := fun _ _ _ => Classical.propDecidable _

noncomputable def f1Observation
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK) :
    Core.Finite.ColdCorridor.EventFamily
      (ReturnStage occurrence member)
      (fun _ => object.Vertex) (fun _ => ULift.{u} (Fin order)) :=
  f1EventFamily occurrence member CycleLengthOK cycleLengthDecidable

/-- Eliminate one exact stored F1 hit into the ambient cycle certificate
carried by its displayed completion.  This performs no new target decision
and constructs no detached graph object. -/
noncomputable def f1CycleCertificateOfHit
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (stage : ReturnStage occurrence member)
    (hit : (f1EventFamily occurrence member CycleLengthOK cycleLengthDecidable).hit
      stage (returnEndpoint occurrence member stage)) :
    Graph.CycleCertificate object CycleLengthOK := by
  let offset := (f1EventFamily occurrence member CycleLengthOK
    cycleLengthDecidable).witness stage
      (returnEndpoint occurrence member stage) hit
  have valid : F1Valid occurrence member CycleLengthOK stage offset.down :=
    (f1EventFamily occurrence member CycleLengthOK cycleLengthDecidable)
      |>.witness_valid stage (returnEndpoint occurrence member stage) hit
  exact Classical.choice (show Nonempty
      (Graph.CycleCertificate object CycleLengthOK) from by
    rcases valid with ⟨returnAdj, isCycle, lengthOK⟩
    exact ⟨{
      vertex := occurrence.1.1 occurrence.1.2.1
      walk := displayedF1Completion occurrence member stage offset.down returnAdj
      isCycle := isCycle
      length_ok := lengthOK }⟩)

/-! A corridor is a graph-owned finite stage schedule.  The return-path
construction is intentionally a contract input: graph theory proves the
schedule and its path laws, while Core/CT machinery scans its events. -/
structure Corridor (object : FiniteObject.{u}) (Item : Type uItem) (State : Type uState)
    [Fintype State] where
  items : Enumeration Item
  items_nonempty : items.values ≠ []
  stages : Item -> Enumeration object.Vertex
  state : Item → State
  /-- The public finite-graph event presentation for this corridor.  Core
  derives all first-failure decisions from these candidate schedules. -/
  observation :
    Core.Finite.ColdCorridor.FourEventObservation.{uItem, u, u} Item

/-! ## Canonical corridor producer from the literal packing

The remaining definitions in this section accept no schedules, paths,
states, or branch outcomes.  Every carrier is generated from one occurrence
of the exact compiler-owned packing profile. -/


abbrev CorridorState (object : FiniteObject.{u}) (order : Nat) :=
  (Fin order × Fin order) ×
    ((Fin 4 → Fin (object.vertexCount + 1)) ×
      (Fin 4 → Fin 4 → Bool))

@[reducible] noncomputable instance corridorStateFintype
    (object : FiniteObject.{u}) (order : Nat) :
    Fintype (CorridorState object order) := by
  exact Fintype.ofFinite _

@[reducible] noncomputable instance corridorStateFinEnum
    (object : FiniteObject.{u}) (order : Nat) :
    FinEnum (CorridorState object order) := by
  letI : DecidableEq (CorridorState object order) := Classical.decEq _
  exact FinEnum.ofEquiv (Fin (Fintype.card (CorridorState object order)))
    (Fintype.equivFin (CorridorState object order))

noncomputable def sameInterfaceTable (object : FiniteObject.{u}) (order : Nat) :
    Enumeration (CorridorState object order) :=
  Enumeration.ofFinEnum (corridorStateFinEnum object order)

/-- Every displayed cut-state is a row: the table is complete, so a consumer
retrieves its row instead of rebuilding one.  This is the finiteness clause of
`def:cold-same-interface-table` ("the table is finite because the support size,
boundary size, window labels, and declared coordinate labels are bounded"). -/
@[simp] theorem mem_sameInterfaceTable
    (object : FiniteObject.{u}) (order : Nat)
    (state : CorridorState object order) :
    state ∈ (sameInterfaceTable object order).values :=
  Enumeration.mem_ofFinEnum_values (corridorStateFinEnum object order) state


noncomputable def returnFrontierTail
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) : object.Vertex :=
  ((selectedReturnPath occurrence member).1.getVert (stage.1 - 1)).1

noncomputable def corridorActiveVertex
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) : Fin 4 → object.Vertex
  | ⟨0, _⟩ => occurrence.1.1 occurrence.1.2.1
  | ⟨1, _⟩ => occurrenceEndpoint occurrence.1
  | ⟨2, _⟩ => returnFrontierTail occurrence member stage
  | ⟨3, _⟩ => returnEndpoint occurrence member stage

noncomputable def corridorBoundaryDegree
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    Fin 4 → Fin (object.vertexCount + 1) :=
  fun index =>
    ⟨object.degree (corridorActiveVertex occurrence member stage index),
      Nat.lt_succ_of_lt
        (object.degree_lt_vertexCount
          (corridorActiveVertex occurrence member stage index))⟩

noncomputable def corridorLocalAdjacency
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) : Fin 4 → Fin 4 → Bool :=
  fun left right =>
    @decide (object.graph.Adj
      (corridorActiveVertex occurrence member stage left)
      (corridorActiveVertex occurrence member stage right))
      (object.decideAdj _ _)

noncomputable def corridorState
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) : CorridorState object order :=
  ((occurrence.1.2.1,
      (successorBoundaryStub occurrence member).1.1.2.1),
    (corridorBoundaryDegree occurrence member stage,
      corridorLocalAdjacency occurrence member stage))

/-- The row of one corridor prefix, retrieved from the table rather than
recomputed: it is the prefix's own displayed cut-state, carrying its table
membership. -/
noncomputable def sameInterfaceRow
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    {row : CorridorState object order //
      row ∈ (sameInterfaceTable object order).values} :=
  ⟨corridorState occurrence member stage, mem_sameInterfaceTable _ _ _⟩

/-! ## Declared cold-interface coordinates

This is the cold-interface subfamily of the paper's declared coordinate
signature: the two window offsets, the boundary-degree profile, and the
complete local incidence table on the four active interface positions.
Labels are retained in the index even when their observed values coincide. -/

abbrev DeclaredColdCoordinate :=
  Sum (Fin 2) (Sum (Fin 4) (Fin 4 × Fin 4))

/-- Canonical complete order of the declared cold-interface coordinates. -/
noncomputable def declaredColdCoordinateSchedule :
    Core.Finite.Enumeration DeclaredColdCoordinate :=
  Core.Finite.Enumeration.ofFinEnum inferInstance

/-- Literal value of one declared coordinate in the active graph corridor.
Boolean incidence values are encoded as `0` or `1`; offsets and degrees keep
their exact natural values. -/
noncomputable def declaredColdCoordinateValue
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    DeclaredColdCoordinate → Nat
  | .inl side =>
      if side.1 = 0 then occurrence.1.2.1.1
      else (successorBoundaryStub occurrence member).1.1.2.1.1
  | .inr (.inl boundary) =>
      (corridorBoundaryDegree occurrence member stage boundary).1
  | .inr (.inr incidence) =>
      if corridorLocalAdjacency occurrence member stage
          incidence.1 incidence.2 then 1 else 0

/-- Exact labelled boundary-response row, evaluated in the canonical
coordinate order from the literal graph and packing occurrence. -/
noncomputable def declaredColdBoundaryResponse
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) : List Nat :=
  declaredColdCoordinateSchedule.values.map
    (declaredColdCoordinateValue occurrence member stage)

theorem declaredColdBoundaryResponse_length
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    (declaredColdBoundaryResponse occurrence member stage).length =
      declaredColdCoordinateSchedule.card := by
  simp [declaredColdBoundaryResponse, Core.Finite.Enumeration.card]

/-- Every entry of the response row is the value of a uniquely scheduled
declared coordinate; no row entry is supplied independently of the graph. -/
theorem declaredColdBoundaryResponse_get
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member)
    (index : Fin declaredColdCoordinateSchedule.card) :
    (declaredColdBoundaryResponse occurrence member stage).get
        (Fin.cast (declaredColdBoundaryResponse_length occurrence member stage).symm
          index) =
      declaredColdCoordinateValue occurrence member stage
        (declaredColdCoordinateSchedule.get index) := by
  simp [declaredColdBoundaryResponse, Core.Finite.Enumeration.get]

/-- One response row together with the literal return stage that generates
it.  The equality field prevents a downstream consumer from substituting an
extensional row detached from the graph. -/
structure DeclaredColdResponseRow
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) where
  stage : ReturnStage occurrence member
  values : List Nat
  values_eq : values = declaredColdBoundaryResponse occurrence member stage

noncomputable def declaredColdResponseRow
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    DeclaredColdResponseRow occurrence member :=
  { stage := stage
    values := declaredColdBoundaryResponse occurrence member stage
    values_eq := rfl }

theorem declaredColdResponseRow_injective
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    Function.Injective (declaredColdResponseRow occurrence member) := by
  intro left right equal
  exact congrArg DeclaredColdResponseRow.stage equal

/-- Canonical complete response-row schedule for all literal return stages of
one packing-owned cold corridor. -/
noncomputable def declaredColdResponseRowSchedule
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    Core.Finite.Enumeration (DeclaredColdResponseRow occurrence member) :=
  (returnStageSchedule occurrence member).map
    (declaredColdResponseRow occurrence member)
    (declaredColdResponseRow_injective occurrence member)
    (Classical.decEq _)

theorem declaredColdResponseRow_mem
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    declaredColdResponseRow occurrence member stage ∈
      (declaredColdResponseRowSchedule occurrence member).values := by
  apply (Core.Finite.Enumeration.mem_map_values
    (returnStageSchedule occurrence member)
    (declaredColdResponseRow occurrence member)
    (declaredColdResponseRow_injective occurrence member)
    (Classical.decEq _)
    (declaredColdResponseRow occurrence member stage)).mpr
  refine ⟨stage, ?_, rfl⟩
  exact List.mem_ofFn.mpr ⟨stage, rfl⟩


/-! ## (G3) The germ support is a connected ambient support

`Core/Strategy/InterfaceReplacement.lean:353`
(`ClosurePayload.noNeutralCompressionFrame`) closes the G3 terminal from a
`CompressionFrame` plus CT7's universal neutrality, and the frame is built by
`Graph.Strategy.InterfaceReplacement.compressionFrameOfIntrinsicWithPresentation`
(`Graph/Strategy/InterfaceReplacement.lean:399`) out of an
`IntrinsicCompressionFrameSupport`, whose first field is exactly
`SupportComponents.Connected.ConnectedOn`.

The germ support is the vertex support of `returnPrefix`, a *path* in the
exterior object, so its connectivity is not an assumption: any two of its
vertices are joined inside it by the sub-walk between them.  The exterior
object is `object.induce (exteriorSupport profile)`, so that sub-walk maps to
the ambient graph along the same induced embedding
`Graph.InducedPathCold.canonicalF5G1Target` uses for the (F1) cycle. -/
/-- The germ support is exactly the ambient image of the return prefix's own
walk support.  Both later germ facts read the support through this
equivalence rather than unfolding the enumeration again. -/
theorem mem_returnPrefixSupport_iff
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) (vertex : object.Vertex) :
    vertex ∈ (returnPrefixSupport occurrence member stage).toFinset ↔
      ∃ interior ∈ (returnPrefix occurrence member stage).support,
        interior.1 = vertex := by
  have supportValues :
      (returnPrefixSupport occurrence member stage).values =
        (returnPrefix occurrence member stage).support.map Subtype.val := rfl
  rw [Enumeration.mem_toFinset, supportValues]
  exact List.mem_map

theorem returnPrefixSupport_connectedOn
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    Graph.SupportComponents.Connected.ConnectedOn object
      (returnPrefixSupport occurrence member stage).toFinset := by
  classical
  letI : DecidableEq (ExteriorObject profile).Vertex :=
    (ExteriorObject profile).vertices.decEq
  have memIff := mem_returnPrefixSupport_iff occurrence member stage
  refine ⟨⟨(exteriorStart occurrence).1, ?_⟩, ?_⟩
  · exact (memIff _).mpr
      ⟨_, (returnPrefix occurrence member stage).start_mem_support, rfl⟩
  · intro left right leftMember rightMember
    obtain ⟨leftInterior, leftSupport, leftValue⟩ := (memIff left).mp leftMember
    obtain ⟨rightInterior, rightSupport, rightValue⟩ :=
      (memIff right).mp rightMember
    subst leftValue
    subst rightValue
    let joined : (ExteriorObject profile).graph.Walk leftInterior rightInterior :=
      ((returnPrefix occurrence member stage).takeUntil
          leftInterior leftSupport).reverse.append
        ((returnPrefix occurrence member stage).takeUntil
          rightInterior rightSupport)
    have joinedSupport : ∀ interior ∈ joined.support,
        interior ∈ (returnPrefix occurrence member stage).support := by
      intro interior interiorMember
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp interiorMember with
        onLeft | onRight
      · exact SimpleGraph.Walk.support_takeUntil_subset_support _ _
          (by simpa using onLeft)
      · exact SimpleGraph.Walk.support_takeUntil_subset_support _ _ onRight
    let ambient := joined.map
      (object.induceEmbedding (exteriorSupport profile)).toHom
    refine ⟨ambient.bypass, ambient.bypass_isPath, ?_⟩
    intro vertex vertexMember
    have onAmbient : vertex ∈ ambient.support :=
      SimpleGraph.Walk.support_bypass_subset_support _ vertexMember
    rw [SimpleGraph.Walk.support_map] at onAmbient
    obtain ⟨interior, interiorMember, interiorValue⟩ :=
      List.mem_map.mp onAmbient
    exact (memIff vertex).mpr
      ⟨interior, joinedSupport interior interiorMember, interiorValue⟩

theorem returnPrefixSupport_proper
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member)
    (interiorNonempty : (interiorPositions order).Nonempty)
    (packed : profile.selected ≠ []) :
    ∃ vertex : object.Vertex,
      vertex ∉ (returnPrefixSupport occurrence member stage).toFinset := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨window, windowMember⟩ :
      ∃ window, window ∈ profile.selected := by
    cases selectedList : profile.selected with
    | nil => exact absurd selectedList packed
    | cons head rest => exact ⟨head, by simp⟩
  obtain ⟨position, positionMember⟩ := interiorNonempty
  refine ⟨window position, ?_⟩
  intro contained
  obtain ⟨interior, _, interiorValue⟩ :=
    (mem_returnPrefixSupport_iff occurrence member stage _).mp contained
  have exteriorMember : window position ∈ exteriorSupport profile := by
    rw [← interiorValue]
    exact interior.2
  have interiorMember : window position ∈ selectedInterior profile :=
    (mem_selectedInterior_iff profile _).mpr
      ⟨window, windowMember,
        Finset.mem_image.mpr ⟨position, positionMember, rfl⟩⟩
  exact (mem_exteriorSupport_iff profile _).mp exteriorMember interiorMember

theorem returnPrefixSupport_subset
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (earlier later : ReturnStage occurrence member)
    (shorter : earlier.1 ≤ later.1) :
    (returnPrefixSupport occurrence member earlier).toFinset ⊆
      (returnPrefixSupport occurrence member later).toFinset := by
  intro vertex membership
  obtain ⟨interior, interiorMember, interiorValue⟩ :=
    (mem_returnPrefixSupport_iff occurrence member earlier vertex).mp membership
  refine (mem_returnPrefixSupport_iff occurrence member later vertex).mpr
    ⟨interior, ?_, interiorValue⟩
  rw [returnPrefix, SimpleGraph.Walk.support_take] at interiorMember ⊢
  have nested :
      (selectedReturnPath occurrence member).1.support.take (earlier.1 + 1) =
        ((selectedReturnPath occurrence member).1.support.take
          (later.1 + 1)).take (earlier.1 + 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  rw [nested] at interiorMember
  exact List.take_subset _ _ interiorMember

/-- The germ support has exactly one vertex per return step, so the nesting
above is strict.  The selected return path is a `Path`, so its support is
nodup and the enumeration's cardinality is its length. -/
theorem returnPrefixSupport_card
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) :
    (returnPrefixSupport occurrence member stage).toFinset.card = stage.1 + 1 := by
  have supportValues :
      (returnPrefixSupport occurrence member stage).values =
        (returnPrefix occurrence member stage).support.map Subtype.val := rfl
  have lengthBound := stage.isLt
  have takeLength : (returnPrefix occurrence member stage).length =
      stage.1 ⊓ (selectedReturnPath occurrence member).1.length :=
    SimpleGraph.Walk.take_length _ _
  have supportLength :
      (returnPrefix occurrence member stage).support.length =
        (returnPrefix occurrence member stage).length + 1 :=
    SimpleGraph.Walk.length_support _
  have cardEq : (returnPrefixSupport occurrence member stage).toFinset.card =
      (returnPrefix occurrence member stage).support.length := by
    rw [Enumeration.card_toFinset, Enumeration.card, supportValues,
      List.length_map]
    rfl
  omega

/-- The strict form consumed by the replacement measure. -/
theorem returnPrefixSupport_ssubset
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (earlier later : ReturnStage occurrence member)
    (shorter : earlier.1 < later.1) :
    (returnPrefixSupport occurrence member earlier).toFinset ⊂
      (returnPrefixSupport occurrence member later).toFinset := by
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨returnPrefixSupport_subset occurrence member earlier later
      (Nat.le_of_lt shorter), ?_⟩
  intro equalSupports
  have cards := congrArg Finset.card equalSupports
  rw [returnPrefixSupport_card occurrence member earlier,
    returnPrefixSupport_card occurrence member later] at cards
  omega

/-- A scheduled exterior branch occurrence exists only inside a selected
window, so the very existence of a cold corridor owner is the packing's
nonemptiness.  `selectedBranchExcess` is
`profile.selected.flatMap …`, which is `[]` on an empty packing. -/
theorem selected_ne_nil_of_exteriorBranch
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    profile.selected ≠ [] := by
  classical
  intro empty
  have scheduled : occurrence.1 ∈ selectedBranchExcess profile := by
    have base := (Enumeration.mem_subtype_values _ _ _ occurrence).mp member
    simpa [selectedBranchExcessSchedule, Enumeration.ofNodupList] using base
  rw [selectedBranchExcess, empty] at scheduled
  simp at scheduled

/-- An occurrence carries a window position (`Graph.InducedPathCold.Token` is
`Sigma fun position : Fin order => …`), so the packing order of a cold corridor
owner is positive.  Like `selected_ne_nil_of_exteriorBranch` this is a
projection of the stored occurrence, not a new hypothesis. -/
theorem order_pos_of_exteriorBranch
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile) : 0 < order :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) occurrence.1.2.1.isLt

noncomputable def returnPrefixSupportAtom
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member)
    (interiorNonempty : (interiorPositions order).Nonempty) :
    Graph.ProperBoundariedAtom object :=
  Graph.Strategy.InterfaceReplacement.SupportAtom.properAtom object
    (returnPrefixSupport occurrence member stage).toFinset
    (returnPrefixSupport_connectedOn occurrence member stage)
    (returnPrefixSupport_proper occurrence member stage interiorNonempty
      (selected_ne_nil_of_exteriorBranch occurrence member))


noncomputable def germStage
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values) :
    ReturnStage occurrence member :=
  (returnStageSchedule occurrence member).get
    ⟨(returnStageSchedule occurrence member).card - 1,
      Nat.sub_lt
        (Nat.pos_of_ne_zero fun zero =>
          returnStageSchedule_nonempty occurrence member
            (List.length_eq_zero_iff.mp (by
              simpa [Core.Finite.Enumeration.card] using zero)))
        Nat.zero_lt_one⟩

/-- The germ site as the framework's own proper boundaried atom: the germ
support's two boundary interfaces, its atom side, and its real complement, all
read off `returnPrefixSupportAtom` at the germ item. -/
noncomputable def germSite
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (interiorNonempty : (interiorPositions order).Nonempty) :
    Graph.ProperBoundariedAtom object :=
  returnPrefixSupportAtom occurrence member (germStage occurrence member)
    interiorNonempty

/-- The completion a corridor prefix represents: the ambient object induced on
the prefix's own retained support.

`def:cold-same-interface-table` (T4) records "the target truth value of every
compatible completion represented by that exact profile", and the completion of
a prefix in the active graph is `object.induce` at its own support -- the same
ambient completion `canonicalF5CT7Spec.Realizes` reads for (G1).  Nothing is
constructed: `returnPrefixSupport` is the stored corridor prefix and
`FiniteObject.induce` is the framework's own induced subobject. -/
noncomputable def germCompletion
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (stage : ReturnStage occurrence member) : FiniteObject.{u} :=
  object.induce (returnPrefixSupport occurrence member stage).toFinset

/-- Exact target response recorded for one corridor prefix: the target truth
value of the completion that prefix represents.

This is the germ's carried "target-response profile" of
`def:cold-bounded-germ`, read on the active graph itself.  No boundary piece,
gluing, or outside context is involved: the row carries its response, and a
consumer that needs the response *in the ambient object* transports it along
`FiniteObject.induceEmbedding`. -/
noncomputable def germTargetResponse
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member) : Bool :=
  @decide (Target (germCompletion occurrence member stage)) (decideTarget _)

/-- The exact target-response defect of two prefixes of one corridor:
`def:cold-corridor-first-failure` (F2)'s "differ in exact target response", on
the two completions those prefixes represent.

This is stated in `Prop` rather than on the decided bits so that it survives
without the `Decidable` instance the scan carries. -/
def F2TargetDefect
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (left right : ReturnStage occurrence member) : Prop :=
  ¬ (Target (germCompletion occurrence member left) ↔
      Target (germCompletion occurrence member right))

/-- Unequal recorded response bits are exactly a typed defect of the two
completions. -/
theorem f2TargetDefect_of_response_ne
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (left right : ReturnStage occurrence member)
    (different :
      germTargetResponse (object := object) (order := order) (profile := profile)
          occurrence member Target decideTarget left ≠
        germTargetResponse (object := object) (order := order) (profile := profile)
          occurrence member Target decideTarget right) :
    F2TargetDefect occurrence member Target left right := by
  unfold F2TargetDefect
  intro same
  apply different
  unfold germTargetResponse
  exact Bool.decide_congr same

def F2Valid
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (candidate : ReturnStage occurrence member) :
    Prop :=
  candidate.1 < stage.1 ∧
    corridorState (object := object) (order := order) (profile := profile)
        occurrence member candidate =
      corridorState (object := object) (order := order) (profile := profile)
        occurrence member stage ∧
      F2TargetDefect occurrence member Target candidate stage

/-- F2 scans every earlier prefix of the same corridor.  Its validity retains
the full corridor-state equality and the literal unequal target response of the
two completions the scanned prefixes represent; Core selects the first such
coordinate. -/
noncomputable def f2EventFamily
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate)) :
    Core.Finite.ColdCorridor.EventFamily
      (ReturnStage occurrence member)
      (fun _ => object.Vertex)
      (fun _ => ULift.{u} (ReturnStage occurrence member)) where
  schedule := fun _ =>
    (returnStageSchedule occurrence member).map
      ULift.up ULift.up_injective (Classical.decEq _)
  valid := fun stage candidate _endpoint =>
    F2Valid occurrence member Target decideTarget stage candidate.down
  valid_decidable := fun _ _ _ => Classical.propDecidable _

/-- Complete Graph interpretation of one stored F2 hit.  Both prefixes are
derived from the selected candidate and belong to the scanned corridor. -/
structure F2Bookkeeping
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (stage : ReturnStage occurrence member) where
  earlier : ReturnStage occurrence member
  earlier_before : earlier.1 < stage.1
  state_eq : corridorState (object := object) (order := order)
      (profile := profile) occurrence member earlier =
    corridorState (object := object) (order := order)
      (profile := profile) occurrence member stage
  defect : F2TargetDefect occurrence member Target earlier stage

/-- Assemble bookkeeping from the literal validity fields of one F2
candidate.  This is a constructor only; candidate selection remains Core's
finite search. -/
noncomputable opaque f2BookkeepingOfValid
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (candidate : ReturnStage occurrence member)
    (valid : F2Valid occurrence member Target decideTarget stage candidate) :
    F2Bookkeeping (object := object) (order := order) (profile := profile)
      occurrence member Target stage := by
  unfold F2Valid at valid
  exact {
    earlier := candidate
    earlier_before := valid.1
    state_eq := valid.2.1
    defect := valid.2.2 }

/-- The candidate carried by Core's one stored F2 hit. -/
noncomputable def f2CandidateOfHit
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (hit : (f2EventFamily occurrence member Target decideTarget).hit
      stage (returnEndpoint occurrence member stage)) :
    ReturnStage occurrence member :=
  ((f2EventFamily occurrence member Target decideTarget).witness
    stage (returnEndpoint occurrence member stage) hit).down

/-- The stored hit's candidate satisfies the named F2 validity predicate. -/
theorem f2CandidateOfHit_valid
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (hit : (f2EventFamily occurrence member Target decideTarget).hit
      stage (returnEndpoint occurrence member stage)) :
    F2Valid occurrence member Target decideTarget stage
      (f2CandidateOfHit occurrence member Target decideTarget stage hit) := by
  unfold f2CandidateOfHit
  exact (f2EventFamily occurrence member Target decideTarget).witness_valid
    stage (returnEndpoint occurrence member stage) hit

/-- A stored Core F2 hit contains complete same-interface Graph bookkeeping.
Both data and validity are projections of the one stored hit; no second search
is evaluated. -/
theorem f2Bookkeeping_nonempty_of_hit
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (hit : (f2EventFamily occurrence member Target decideTarget).hit
      stage (returnEndpoint occurrence member stage)) :
    Nonempty (F2Bookkeeping (object := object) (order := order)
      (profile := profile) occurrence member Target stage) := by
  let candidate := f2CandidateOfHit occurrence member Target decideTarget
    stage hit
  have valid := f2CandidateOfHit_valid occurrence member Target decideTarget
    stage hit
  exact ⟨f2BookkeepingOfValid occurrence member Target decideTarget
    stage candidate valid⟩

/-- Canonical proof-irrelevant elimination of the stored F2 hit. -/
noncomputable def f2BookkeepingOfHit
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (hit : (f2EventFamily occurrence member Target decideTarget).hit
      stage (returnEndpoint occurrence member stage)) :
    F2Bookkeeping (object := object) (order := order) (profile := profile)
      occurrence member Target stage :=
  Classical.choice (f2Bookkeeping_nonempty_of_hit occurrence member Target
    decideTarget stage hit)

/-- Literal semantic validity of one F3 candidate.  Unlike the repeated-state
alternative used by F5, an F3 candidate is already a genuine graph-local
replacement of the germ site: `def:cold-corridor-first-failure` (F3) is "two
prefixes have the same exact target response against every outside context and
one gives a strictly smaller proper representative", which is exactly
`Graph.Strategy.InterfaceReplacement.IntrinsicCompressibleSupport` at the
scanned germ's own support.  Equality of the displayed cold state is retained
as the paper's window/interface compatibility check. -/
def F3Valid
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (stage : ReturnStage occurrence member)
    (candidate : ReturnStage occurrence member) :
    Prop :=
  candidate.1 < stage.1 ∧
    corridorState occurrence member candidate =
      corridorState occurrence member stage ∧
    Graph.Strategy.InterfaceReplacement.IntrinsicCompressibleSupport
      Target object (returnPrefixSupport occurrence member stage).toFinset

/-- F3 scans the same literal earlier-prefix schedule as F2, but its predicate
is the full replacement certificate rather than the negation of an F2 response
defect.  Core therefore records a real compression witness and a plain repeated
state remains available to the F5 bounded-outcome split. -/
noncomputable def f3EventFamily
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate)) :
    Core.Finite.ColdCorridor.EventFamily
      (ReturnStage occurrence member)
      (fun _ => object.Vertex)
      (fun _ => ULift.{u} (ReturnStage occurrence member)) where
  schedule := fun _ =>
    (returnStageSchedule occurrence member).map
      ULift.up ULift.up_injective (Classical.decEq _)
  valid := fun stage candidate _endpoint =>
    F3Valid occurrence member Target stage candidate.down
  valid_decidable := fun _ _ _ => Classical.propDecidable _

/-- Complete typed bookkeeping recovered from Core's stored F3 hit.  No
replacement, context, or semantic proof is recomputed after classification. -/
structure F3Bookkeeping
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (stage : ReturnStage occurrence member) where
  earlier : ReturnStage occurrence member
  valid : F3Valid occurrence member Target stage earlier

/-- The exact target-complete compression of the germ support carried by the
stored (F3) event.  This is `lem:cold-corridor-first-failure` (iii)'s "smaller
target-complete representative of a proper support", read back off the ledger
and never recomputed. -/
theorem F3Bookkeeping.compressible
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    {occurrence : ExteriorBranchOccurrence profile}
    {member : occurrence ∈ (exteriorBranchSchedule profile).values}
    {Target : FiniteObject.{u} → Prop}
    {stage : ReturnStage occurrence member}
    (bookkeeping : F3Bookkeeping occurrence member Target stage) :
    Graph.Strategy.InterfaceReplacement.IntrinsicCompressibleSupport
      Target object (returnPrefixSupport occurrence member stage).toFinset :=
  bookkeeping.valid.2.2

theorem F3Bookkeeping.properRepresentative
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    {occurrence : ExteriorBranchOccurrence profile}
    {member : occurrence ∈ (exteriorBranchSchedule profile).values}
    {Target : FiniteObject.{u} → Prop}
    {stage : ReturnStage occurrence member}
    (bookkeeping : F3Bookkeeping occurrence member Target stage) :
    ∃ vertex : object.Vertex,
      vertex ∉ (returnPrefixSupport occurrence member stage).toFinset := by
  obtain ⟨_connected, proper, _rest⟩ := bookkeeping.compressible
  exact proper

/-- The target-free structural frame of the stored (F3) compression, in Core's
own pre-scan shape.  Consumes
`Graph.Strategy.InterfaceReplacement.intrinsicCompressionFrameOfCompressible`
at the point of use; nothing is restated here. -/
theorem F3Bookkeeping.compressionFrame
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    {occurrence : ExteriorBranchOccurrence profile}
    {member : occurrence ∈ (exteriorBranchSchedule profile).values}
    {Target : FiniteObject.{u} → Prop}
    {stage : ReturnStage occurrence member}
    (bookkeeping : F3Bookkeeping occurrence member Target stage) :
    Graph.Strategy.InterfaceReplacement.IntrinsicCompressionFrameSupport
      object (returnPrefixSupport occurrence member stage).toFinset :=
  Graph.Strategy.InterfaceReplacement.intrinsicCompressionFrameOfCompressible
    Target object _ bookkeeping.compressible

/-- Assemble the F3 bookkeeping from one candidate whose validity was stored
by Core.  The constructor performs no search or response comparison. -/
noncomputable opaque f3BookkeepingOfValid
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (candidate : ReturnStage occurrence member)
    (valid : F3Valid occurrence member Target stage candidate) :
    F3Bookkeeping occurrence member Target stage := by
  exact { earlier := candidate, valid }

/-- The candidate carried by Core's one stored F3 hit. -/
noncomputable def f3CandidateOfHit
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (hit : (f3EventFamily occurrence member Target decideTarget).hit
      stage (returnEndpoint occurrence member stage)) :
    ReturnStage occurrence member :=
  ((f3EventFamily occurrence member Target decideTarget).witness
    stage (returnEndpoint occurrence member stage) hit).down

/-- Core's stored F3 witness satisfies the exact semantic predicate. -/
theorem f3CandidateOfHit_valid
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (hit : (f3EventFamily occurrence member Target decideTarget).hit
      stage (returnEndpoint occurrence member stage)) :
    F3Valid occurrence member Target stage
      (f3CandidateOfHit occurrence member Target decideTarget stage hit) := by
  unfold f3CandidateOfHit
  exact (f3EventFamily occurrence member Target decideTarget).witness_valid
    stage (returnEndpoint occurrence member stage) hit

/-- Eliminate one exact Core-selected F3 hit into its target-complete strict
replacement payload. -/
noncomputable def f3BookkeepingOfHit
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    (stage : ReturnStage occurrence member)
    (hit : (f3EventFamily occurrence member Target decideTarget).hit
      stage (returnEndpoint occurrence member stage)) :
    F3Bookkeeping occurrence member Target stage :=
  f3BookkeepingOfValid occurrence member Target decideTarget stage
    (f3CandidateOfHit occurrence member Target decideTarget stage hit)
    (f3CandidateOfHit_valid occurrence member Target decideTarget stage hit)

/-- F4 is first entry into a carrier already present in the incoming handoff
ledger.  Candidates are the attached members of that exact residual-owned
**item** schedule -- the producer's own entries, not a decoded vertex set --
so every stored F4 witness retains the literal producer item together with its
membership in the predecessor ledger.  The vertex support each item names is
read through `handoffSupport`, which is the producer's own decoding and is
never inverted here. -/
noncomputable def f4EventFamily
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    Core.Finite.ColdCorridor.EventFamily
      (ReturnStage occurrence member)
      (fun _ => object.Vertex)
      (fun _ => {item : Handoff // item ∈ handoffItems.values}) where
  schedule := fun _ => handoffItems.attach
  valid := fun _stage item endpoint => endpoint ∈ handoffSupport item.1
  valid_decidable := fun _ _ _ => Classical.propDecidable _

/-- Every F4 hit is literally an entry into the carrier of one item of the
incoming handoff schedule.  Both conjuncts are projections of Core's stored
search witness; no item and no support is reconstructed after classification. -/
theorem f4Witness_exact
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : ReturnStage occurrence member)
    (hit : (f4EventFamily occurrence member handoffItems handoffSupport).hit
      stage (returnEndpoint occurrence member stage)) :
    let item := (f4EventFamily occurrence member handoffItems
      handoffSupport).witness stage
        (returnEndpoint occurrence member stage) hit
    item.1 ∈ handoffItems.values ∧
      returnEndpoint occurrence member stage ∈ handoffSupport item.1 := by
  dsimp only
  constructor
  · exact Subtype.property _
  · exact (f4EventFamily occurrence member handoffItems
      handoffSupport).witness_valid
      stage (returnEndpoint occurrence member stage) hit

noncomputable def canonicalObservation
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    Core.Finite.ColdCorridor.FourEventObservation.{0, u, u}
      (ReturnStage occurrence member) where
  Output := fun _ => object.Vertex
  run := returnEndpoint occurrence member
  F1Candidate := fun _ => ULift.{u} (Fin order)
  F2Candidate := fun _ => ULift.{u} (ReturnStage occurrence member)
  F3Candidate := fun _ => ULift.{u} (ReturnStage occurrence member)
  F4Candidate := fun _ => {item : Handoff // item ∈ handoffItems.values}
  f1 := f1EventFamily occurrence member CycleLengthOK cycleLengthDecidable
  f2 := f2EventFamily occurrence member Target decideTarget
  f3 := f3EventFamily occurrence member Target decideTarget
  f4 := f4EventFamily occurrence member handoffItems handoffSupport

/-- Complete graph-owned cold corridor.  Core obtains its prefix order from
the selected return path, computes all four searches, derives F5 as their
complement, and records the finite response state. -/
noncomputable def canonicalCorridor
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    Corridor object (ReturnStage occurrence member)
      (CorridorState object order) := by
  let stages := returnStageSchedule occurrence member
  have stages_nonempty : stages.values ≠ [] := by
    exact returnStageSchedule_nonempty occurrence member
  exact {
    items := stages
    items_nonempty := stages_nonempty
    stages := returnPrefixSupport occurrence member
    state := corridorState occurrence member
    observation := canonicalObservation occurrence member
      CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport }

/-! The graph-owned interpretation of the reusable Core first-failure scan.
The four genuine event predicates are observations of one literal corridor
item; Core derives the complementary F5 branch and owns the ordered scan. -/
structure FirstFailurePresentation (object : FiniteObject.{u})
    (Item : Type uItem) (State : Type uState) [Fintype State]
    (corridor : Corridor object Item State) where

/-- Canonical pointwise presentation.  All schedules, states, event families,
and observations are computed by `canonicalCorridor`; the empty wrapper only
selects the existing Core interpretation. -/
noncomputable def canonicalFirstFailurePresentation
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    FirstFailurePresentation object
      (ReturnStage occurrence member) (CorridorState object order)
      (canonicalCorridor occurrence member CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) := by
  exact {}

noncomputable def FirstFailurePresentation.coreContract
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState} [Fintype State]
    {corridor : Corridor object Item State}
  (presentation : FirstFailurePresentation object Item State corridor) :
    Core.Finite.ColdCorridor.Contract Item :=
  Core.Finite.ColdCorridor.Contract.ofObservation
    corridor.items corridor.observation

/-- The F2 event stored by the canonical pointwise contract is exactly the
graph-owned F2 hit; consumers use this projection instead of unfolding the
sealed corridor. -/
@[simp] theorem canonicalFirstFailurePresentation_f2Hit
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : ReturnStage occurrence member) :
    let contract := (canonicalFirstFailurePresentation occurrence member
      CycleLengthOK cycleLengthDecidable Target decideTarget
      handoffItems handoffSupport).coreContract
    contract.f2 stage (contract.run stage) ↔
      (f2EventFamily occurrence member Target decideTarget).hit stage
        (returnEndpoint occurrence member stage) := Iff.rfl

set_option maxHeartbeats 1000000 in
/-- Read a stored Core F1 event from the canonical graph corridor and recover
its exact ambient cycle certificate.  The displayed completion and every
proof used here are carried by the event's stored `sound` field. -/
noncomputable def f1CycleCertificateOfStoredEvent
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (event : Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation occurrence member CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport).coreContract
      .f1) :
    Graph.CycleCertificate object CycleLengthOK := by
  apply f1CycleCertificateOfHit occurrence member CycleLengthOK
    cycleLengthDecidable event.item
  exact event.sound

/-- Generic target lift for the stored F1 route.  The cold strategy supplies
the left disjunct from its exact cycle ledger witness; the surrounding proof
may choose any right-hand frontier proposition without being inspected or
decided here. -/
theorem f1StoredEventDisjunctiveTarget
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (event : Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation occurrence member CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport).coreContract
      .f1)
    (Rest : FiniteObject.{u} → Prop) :
    Graph.HasCycleWithLength CycleLengthOK object ∨ Rest object :=
  Or.inl ⟨f1CycleCertificateOfStoredEvent occurrence member CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport event⟩

set_option maxHeartbeats 1000000 in
/-- Read a stored Core F2 event from the canonical graph corridor and recover
its complete Graph bookkeeping.  The event item is the later return stage;
its `sound` field is definitionally the F2-family hit from which the earlier
stage, common context support, displayed-interface equality, and target
defect are projected. -/
noncomputable def f2BookkeepingOfStoredEvent
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (event : Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation occurrence member CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport).coreContract
      .f2) :
    F2Bookkeeping (object := object) (order := order) (profile := profile)
      occurrence member Target event.item := by
  apply f2BookkeepingOfHit occurrence member Target decideTarget event.item
  exact event.sound

set_option maxHeartbeats 1000000 in
/-- Read a stored Core F3 event from the canonical graph corridor and recover
the exact target-complete strict replacement selected by that event. -/
noncomputable def f3BookkeepingOfStoredEvent
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (event : Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation occurrence member CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport).coreContract
      .f3) :
    F3Bookkeeping occurrence member Target event.item := by
  apply f3BookkeepingOfHit occurrence member Target decideTarget event.item
  exact event.sound

/-- Read a stored Core F4 event as the exact member of the incoming handoff
schedule that it selected.  Both membership and endpoint incidence are
projections of the stored hit. -/
noncomputable def f4EntryOfStoredEvent
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (event : Core.Finite.ColdCorridor.Contract.EventWitness
      (canonicalFirstFailurePresentation occurrence member CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport).coreContract
      .f4) :
    {item : Handoff //
      item ∈ handoffItems.values ∧
        returnEndpoint occurrence member event.item ∈
          handoffSupport item} := by
  let hit : (f4EventFamily occurrence member handoffItems handoffSupport).hit
      event.item (returnEndpoint occurrence member event.item) := event.sound
  let entry := (f4EventFamily occurrence member handoffItems
    handoffSupport).witness
    event.item (returnEndpoint occurrence member event.item) hit
  exact ⟨entry.1,
    f4Witness_exact occurrence member handoffItems handoffSupport
      event.item hit⟩

/-- The public graph adapter exposes Core's typed first-failure/F5 terminal
classification directly; no graph executor reclassifies the corridor. -/
noncomputable def FirstFailurePresentation.classification
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState} [Fintype State]
    {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    Core.Finite.ColdCorridor.Contract.Classification
      presentation.coreContract :=
  Core.Finite.ColdCorridor.Contract.classification presentation.coreContract

/-! The exact scheduled owner type retains the proof that each corridor came
from the literal branch-excess schedule. -/
abbrev ScheduledExteriorBranch
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  {occurrence : ExteriorBranchOccurrence profile //
    occurrence ∈ (exteriorBranchSchedule profile).values}

noncomputable def scheduledExteriorBranches
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (ScheduledExteriorBranch profile) :=
  (exteriorBranchSchedule profile).attach

abbrev AmbientCubicScheduledExteriorBranch
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  {owner : ScheduledExteriorBranch profile //
    ∀ position : Fin order,
      object.degree (owner.1.1.1 position) = 3}

/-- Exact residual-derived schedule of ambient-cubic branch-excess owners. -/
noncomputable def ambientCubicScheduledExteriorBranches
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (AmbientCubicScheduledExteriorBranch profile) :=
  (scheduledExteriorBranches profile).subtype
    (fun owner => ∀ position : Fin order,
      object.degree (owner.1.1.1 position) = 3)
    (fun _ => Classical.propDecidable _)

/-- The fifteen-stub identity is read from the cubic proof carried by one
owner of the residual-derived schedule.  No window is selected or rebuilt. -/
theorem ambientCubicOwner_externalStubCount
    {object : FiniteObject.{u}}
    {profile : InducedPathMaximalPacking.Profile object 13}
    (owner : AmbientCubicScheduledExteriorBranch profile) :
    externalStubCount owner.1.1.1.1 = 15 :=
  externalStubCount_p13_of_cubic owner.1.1.1.1 owner.2

/-- Removing the two canonical transit stubs leaves exactly thirteen
branch-excess entries for every owner already present in the cubic residual
schedule. -/
theorem ambientCubicOwner_branchExcessLength
    {object : FiniteObject.{u}}
    {profile : InducedPathMaximalPacking.Profile object 13}
    (owner : AmbientCubicScheduledExteriorBranch profile) :
    (branchExcess owner.1.1.1.1 2).length = 13 :=
  branchExcess_length_p13_of_cubic owner.1.1.1.1 owner.2

/-- Graph specialization of Core's finite corridor-family producer.  It reads
the literal packing-derived branch schedule, restricts it to the
ambient-cubic owners carried by that schedule, constructs each canonical
return path, and delegates every F1--F5 decision to the existing Core
producer. -/
noncomputable def canonicalFamilyProducer
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    Core.Finite.ColdCorridor.Producer.FamilyProducer
      (AmbientCubicScheduledExteriorBranch profile) where
  owners := ambientCubicScheduledExteriorBranches profile
  Item := fun owner => ReturnStage owner.1.1 owner.1.2
  State := fun _owner => CorridorState object order
  stateFintype := fun _owner => inferInstance
  producer := fun owner => by
    let corridor := canonicalCorridor owner.1.1 owner.1.2 CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    exact Core.Finite.ColdCorridor.Producer.ofObservation
      { schedule := corridor.items
        state := corridor.state }
      corridor.observation

@[simp] theorem canonicalFamilyProducer_trace_schedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (owner : AmbientCubicScheduledExteriorBranch profile) :
    (@Core.Finite.ColdCorridor.Contract.StateTrace.schedule
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).Item owner)
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).State owner)
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).stateFintype owner)
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).traceAt owner)) =
        returnStageSchedule owner.1.1 owner.1.2 := rfl

@[simp] theorem canonicalFamilyProducer_trace_state
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (owner : AmbientCubicScheduledExteriorBranch profile) :
    (@Core.Finite.ColdCorridor.Contract.StateTrace.state
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).Item owner)
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).State owner)
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).stateFintype owner)
      ((canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).traceAt owner)) =
        corridorState owner.1.1 owner.1.2 := rfl

/-- The F2 projection of the pointwise contract exposed by the canonical
family, stated without unfolding the sealed corridor implementation. -/
@[simp] theorem canonicalFamilyProducer_contract_f2Hit
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (owner : AmbientCubicScheduledExteriorBranch profile)
    (stage : ReturnStage owner.1.1 owner.1.2) :
    let contract := (canonicalFamilyProducer profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport).contractAt owner
    contract.f2 stage (contract.run stage) ↔
      (f2EventFamily owner.1.1 owner.1.2 Target decideTarget).hit stage
        (returnEndpoint owner.1.1 owner.1.2 stage) := Iff.rfl

set_option maxHeartbeats 2000000 in
/-- The F3 projection of the pointwise contract exposed by the canonical
family, the (F3) counterpart of `canonicalFamilyProducer_contract_f2Hit`. -/
@[simp] theorem canonicalFamilyProducer_contract_f3Hit
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (owner : AmbientCubicScheduledExteriorBranch profile)
    (stage : ReturnStage owner.1.1 owner.1.2) :
    let contract := (canonicalFamilyProducer profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport).contractAt owner
    contract.f3 stage (contract.run stage) ↔
      (f3EventFamily owner.1.1 owner.1.2 Target decideTarget).hit stage
        (returnEndpoint owner.1.1 owner.1.2 stage) := Iff.rfl


/-! ## F5 bounded-germ response classification

The following definitions only instantiate existing residual focus and CT7
objects.  CT7 runs on an `ActiveView` of the literal classified-family stage;
its generated payload is then appended to that stage by `Focus.runCountedPayload`.
No detached root or copied cold payload occurs in this continuation. -/

/-- Orient the two literal strands retained by Core's bounded outcome.  A
repeated outcome uses its stored ordered repeated-state pair.  A terminal
outcome uses the last and first stages of that exact terminal corridor; in
particular it never manufactures the former degenerate `terminal/terminal`
pair. -/
noncomputable def boundedOutcomeRepresentatives
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    {State : Type uState} [Fintype State]
    (trace : Core.Finite.ColdCorridor.Contract.StateTrace
      (ReturnStage occurrence member) State)
    (trace_nonempty : trace.schedule.values ≠ [])
    (outcome : trace.BoundedOutcome) :
    Core.Response.Representatives (ReturnStage occurrence member) :=
  match outcome with
  | .terminal _ =>
      let firstIndex : Fin trace.schedule.card :=
        ⟨0, Nat.pos_of_ne_zero fun zero =>
          trace_nonempty (List.length_eq_zero_iff.mp (by
            simpa [Core.Finite.Enumeration.card] using zero))⟩
      let terminalIndex : Fin trace.schedule.card :=
        ⟨trace.schedule.card - 1, Nat.sub_lt
          (by
            exact Nat.pos_of_ne_zero fun zero =>
              trace_nonempty (List.length_eq_zero_iff.mp (by
                simpa [Core.Finite.Enumeration.card] using zero)))
          Nat.zero_lt_one⟩
      let terminal := trace.schedule.get terminalIndex
      let initial := trace.schedule.get firstIndex
      { source := terminal
        replacement := initial }
  | .repeated repeated =>
      { source := repeated.prefixTrace.schedule.get repeated.pair.2
        replacement := repeated.prefixTrace.schedule.get repeated.pair.1 }

/-- The representative pair of a stored repeated outcome is exactly the pair
carried by that outcome.  This is an elimination rule for the ledger value;
it does not run the bounded-state decision again. -/
theorem boundedOutcomeRepresentatives_of_repeated
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    {State : Type uState} [Fintype State]
    (trace : Core.Finite.ColdCorridor.Contract.StateTrace
      (ReturnStage occurrence member) State)
    (trace_nonempty : trace.schedule.values ≠ [])
    (outcome : trace.BoundedOutcome)
    (selected : outcome.IsRepeated) :
    let repeated := outcome.repeatedWitnessOf selected
    (boundedOutcomeRepresentatives occurrence member trace trace_nonempty
        outcome).source =
        repeated.prefixTrace.schedule.get repeated.pair.2 ∧
      (boundedOutcomeRepresentatives occurrence member trace trace_nonempty
        outcome).replacement =
        repeated.prefixTrace.schedule.get repeated.pair.1 := by
  cases outcome with
  | terminal bounded => exact False.elim selected
  | repeated witness => exact ⟨rfl, rfl⟩

/-- The terminal representative pair is read from the two endpoints of the
same stored terminal trace.  This theorem is an elimination rule for the
ledger outcome and performs no second bounded-state decision. -/
theorem boundedOutcomeRepresentatives_of_terminal
    {object : FiniteObject.{u}} {order : Nat}
    {profile : InducedPathMaximalPacking.Profile object order}
    (occurrence : ExteriorBranchOccurrence profile)
    (member : occurrence ∈ (exteriorBranchSchedule profile).values)
    {State : Type uState} [Fintype State]
    (trace : Core.Finite.ColdCorridor.Contract.StateTrace
      (ReturnStage occurrence member) State)
    (trace_nonempty : trace.schedule.values ≠ [])
    (outcome : trace.BoundedOutcome)
    (selected : outcome.IsTerminal) :
    let firstIndex : Fin trace.schedule.card :=
      ⟨0, Nat.pos_of_ne_zero fun zero =>
        trace_nonempty (List.length_eq_zero_iff.mp (by
          simpa [Core.Finite.Enumeration.card] using zero))⟩
    let terminalIndex : Fin trace.schedule.card :=
      ⟨trace.schedule.card - 1, Nat.sub_lt
        (Nat.pos_of_ne_zero fun zero =>
          trace_nonempty (List.length_eq_zero_iff.mp (by
            simpa [Core.Finite.Enumeration.card] using zero)))
        Nat.zero_lt_one⟩
    (boundedOutcomeRepresentatives occurrence member trace trace_nonempty
        outcome).source = trace.schedule.get terminalIndex ∧
      (boundedOutcomeRepresentatives occurrence member trace trace_nonempty
        outcome).replacement = trace.schedule.get firstIndex := by
  cases outcome with
  | terminal bounded => exact ⟨rfl, rfl⟩
  | repeated witness => exact False.elim selected

/-- A packing-owned corridor member carrying its exact membership proof. -/
abbrev CanonicalColdOwner
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  { owner : AmbientCubicScheduledExteriorBranch profile //
    owner ∈ (ambientCubicScheduledExteriorBranches profile).values }

/-- Return-stage type indexed by one exact attached cold owner. -/
abbrev CanonicalColdStage
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (owner : CanonicalColdOwner profile) :=
    ReturnStage owner.1.1.1 owner.1.1.2

/-- CT7 representatives are dependent functions over the exact attached
owner schedule.  This lets one CT7 execution classify every F5 corridor at
once while keeping every return stage indexed by its original owner. -/
abbrev CanonicalColdRepresentative
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  (owner : CanonicalColdOwner profile) → CanonicalColdStage profile owner

abbrev CanonicalColdContext
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :=
  Sigma fun _owner : CanonicalColdOwner profile => DeclaredColdCoordinate

/-- The complete owner-major CT7 coordinate schedule, obtained by flattening
the attached producer schedule against the registered declared cold-interface
coordinate schedule. -/
noncomputable def canonicalColdContextSchedule
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order) :
    Enumeration (CanonicalColdContext profile) :=
  (Core.Finite.DependentEnumeration.mk
    (ambientCubicScheduledExteriorBranches profile).attach
    (fun _owner => declaredColdCoordinateSchedule)).flatten

/- Seal the canonical family term.

`Contract.Family.FailureOwner` (`Core/Finite/ColdCorridor.lean:1404`) is a
reducible subtype whose property mentions `family.contractAt owner.1`, so every
projection into a stored owner drove `whnf` through `contractAt`, into
`canonicalFamilyProducer.producer`, and on into the corridor construction below.
That is what forced `maxHeartbeats 0` on the cold closures.

The seal is placed on `canonicalCorridor` rather than on the family record: the
record's `owners`, `Item` and `State` projections are cheap and *are* needed
definitionally (`CanonicalColdOwner` is the subtype over `owners.values`), while
the corridor body is the expensive part and is consumed only through the
framework's own query API.  No statement changes. -/
attribute [irreducible] canonicalCorridor

/-- The canonical family used throughout the residual-native F5 continuation. -/
noncomputable abbrev CanonicalColdFamily
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :=
  canonicalFamilyProducer profile CycleLengthOK cycleLengthDecidable
    Target decideTarget handoffItems handoffSupport

/-- Focus exactly the classified cold stages whose stored F5-owner schedule
is nonempty.  The selector reads the newest ledger entry and records no new
mathematical datum.  The terminal/repeated distinction remains available
through the two exact bounded-outcome subqueries. -/
noncomputable def canonicalF5Focus
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    Core.Residual.Focus.Profile
      ((CanonicalColdFamily profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous) := by
  let family := CanonicalColdFamily profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  let parent := Core.Residual.Focus.always
    (family.ClassifiedStateStage Previous)
  let owners := Core.Residual.Focus.ActiveQuery.ofQuery
    (profile := parent) family.storedSurvivingOwnersQuery
  let refinement : Core.Residual.Focus.Refinement parent :=
    Core.Residual.Focus.Refinement.ofDecision
      (fun stage active => (owners.read stage active).values ≠ [])
      (fun stage active =>
        { value := Classical.propDecidable ((owners.read stage active).values ≠ [])
          checks := 1 })
      (Core.PolynomialCheckBudget.constant (fun _stage => 0) 1)
      (fun _stage _active => rfl)
  exact Core.Residual.Focus.refine parent refinement

/-- Read one representative pair solely from the active classified ledger
entry.  The dependent owner index is retained, so the stored bounded outcome
and its return stages cannot be detached from the incoming residual. -/
noncomputable def canonicalF5RepresentativePair
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner : CanonicalColdOwner profile) :
    Core.Response.Representatives (CanonicalColdStage profile owner) := by
  let family := CanonicalColdFamily profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  let classification := family.storedClassificationQuery.read view.previous
  letI := family.stateFintype owner.1
  if selected : Core.Finite.ColdCorridor.Contract.Classification.IsFailure
      (family.contractAt owner.1)
      (classification.classify owner) .f5 then
    let f5Owner : family.F5Owner classification := ⟨owner, selected⟩
    exact boundedOutcomeRepresentatives owner.1.1.1 owner.1.1.2
      (family.traceAt owner.1)
      (by
        simpa [family] using
          returnStageSchedule_nonempty owner.1.1.1 owner.1.1.2)
      (family.storedF5BoundedOutcome view.previous f5Owner)
  else
    match classified : classification.classify owner with
    | .hit witness => exact ⟨witness.item, witness.item⟩
    | .f5 all =>
        have f5Selected :
            Core.Finite.ColdCorridor.Contract.Classification.IsFailure
              (family.contractAt owner.1)
              (classification.classify owner) .f5 := by
          rw [classified]
          rfl
        exact (selected f5Selected).elim

/-- Read the two representative functions solely from the active classified
stage.  F5 owners use their stored bounded outcome.  Every non-F5 owner uses
the exact first-hit item stored by its classification on both sides; no
default return stage is constructed and such owners cannot create a CT7 hit
or distinction. -/
noncomputable def canonicalF5Representatives
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport)) :
    Core.Response.Representatives (CanonicalColdRepresentative profile) := by
  exact
    { source := fun owner =>
        (canonicalF5RepresentativePair profile CycleLengthOK
          cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner).source
      replacement := fun owner =>
        (canonicalF5RepresentativePair profile CycleLengthOK
          cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner).replacement }

/-- Earlier item of the exact repeated-state pair stored for one selected F5
owner.  This is a dependent projection of the active ledger outcome. -/
noncomputable def canonicalRepeatedEarlier
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner :
      let family := CanonicalColdFamily profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous)) :
    CanonicalColdStage profile owner.1.1 := by
  let family := CanonicalColdFamily profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  let repeated := family.storedRepeatedF5Witness view.previous owner
  exact repeated.prefixTrace.schedule.get repeated.pair.1

/-- Later item of the same exact repeated-state pair. -/
noncomputable def canonicalRepeatedLater
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner :
      let family := CanonicalColdFamily profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous)) :
    CanonicalColdStage profile owner.1.1 := by
  let family := CanonicalColdFamily profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  let repeated := family.storedRepeatedF5Witness view.previous owner
  exact repeated.prefixTrace.schedule.get repeated.pair.2

/-- On a repeated-state owner selected by the stored repeated-F5 query, CT7's
two representatives are exactly the ordered pair in that same ledger
outcome.  This is the bridge used by G3; no stage is selected a second time. -/
theorem canonicalF5Representatives_at_repeated
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner :
      let family := CanonicalColdFamily profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous)) :
    let representatives := canonicalF5Representatives profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport view
    representatives.source owner.1.1 =
        canonicalRepeatedLater profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner ∧
      representatives.replacement owner.1.1 =
        canonicalRepeatedEarlier profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner := by
  dsimp only
  let family := CanonicalColdFamily profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  have selected : Core.Finite.ColdCorridor.Contract.Classification.IsFailure
      (family.contractAt owner.1.1.1)
      ((family.storedClassificationQuery.read view.previous).classify
        owner.1.1) .f5 := by
    exact owner.1.2
  unfold canonicalF5Representatives
  change
    (canonicalF5RepresentativePair profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport view
        owner.1.1).source =
        canonicalRepeatedLater profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner ∧
      (canonicalF5RepresentativePair profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport view
        owner.1.1).replacement =
        canonicalRepeatedEarlier profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport view owner
  unfold canonicalF5RepresentativePair
  rw [dif_pos selected]
  let outcome := family.storedF5BoundedOutcome view.previous owner.1
  have repeatedSelected : outcome.IsRepeated := owner.2
  have selected_eq : selected = owner.1.2 := Subsingleton.elim _ _
  cases selected_eq
  unfold canonicalRepeatedEarlier canonicalRepeatedLater
  dsimp only
  convert boundedOutcomeRepresentatives_of_repeated owner.1.1.1.1.1
      owner.1.1.1.1.2 (family.traceAt owner.1.1.1)
      (by
        simpa [family] using returnStageSchedule_nonempty
          owner.1.1.1.1.1 owner.1.1.1.1.2)
      outcome repeatedSelected using 1 <;> rfl

/- The corridor is sealed (`attribute [irreducible] canonicalCorridor` above),
so `repeated.originalIndex` keeps its `Fin (family.traceAt owner).schedule.card`
index instead of collapsing to `Fin (returnStageSchedule ..).card` by `whnf`.
`canonicalFamilyProducer_trace_schedule` identifies the schedules, and Core's
`Enumeration.castIndex` transports the dependent index without unfolding the
corridor. -/
/-- The exact repeated-F5 query carries the paper's strict prefix orientation
and equal finite corridor state.  Both conclusions are projections of the
stored bounded outcome and the registered return-stage schedule. -/
theorem canonicalRepeatedF5Witness_facts
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (owner :
      let family := CanonicalColdFamily profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous)) :
    let earlier := canonicalRepeatedEarlier profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner
    let later := canonicalRepeatedLater profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner
    earlier.1 < later.1 ∧
      corridorState owner.1.1.1.1.1 owner.1.1.1.1.2 earlier =
        corridorState owner.1.1.1.1.1 owner.1.1.1.1.2 later := by
  dsimp only
  let family := CanonicalColdFamily profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  let repeated := family.storedRepeatedF5Witness view.previous owner
  have traceSchedule :
      (family.traceAt owner.1.1.1).schedule =
        returnStageSchedule owner.1.1.1.1.1 owner.1.1.1.1.2 :=
    canonicalFamilyProducer_trace_schedule profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1
  have traceState :
      (family.traceAt owner.1.1.1).state =
        corridorState owner.1.1.1.1.1 owner.1.1.1.1.2 :=
    canonicalFamilyProducer_trace_state profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport owner.1.1.1
  have traceGetVal
      (index : Fin (family.traceAt owner.1.1.1).schedule.card) :
      ((family.traceAt owner.1.1.1).schedule.get index).1 = index.1 := by
    calc
      ((family.traceAt owner.1.1.1).schedule.get index).1 =
          ((returnStageSchedule owner.1.1.1.1.1
            owner.1.1.1.1.2).get
              (Enumeration.castIndex traceSchedule index)).1 := by
        exact congrArg (fun stage => stage.1)
          (Enumeration.get_castIndex traceSchedule index).symm
      _ = (Enumeration.castIndex traceSchedule index).1 := by
        exact returnStageSchedule_get_val owner.1.1.1.1.1
          owner.1.1.1.1.2 (Enumeration.castIndex traceSchedule index)
      _ = index.1 := Enumeration.castIndex_val traceSchedule index
  change (repeated.prefixTrace.schedule.get repeated.pair.1).1 <
      (repeated.prefixTrace.schedule.get repeated.pair.2).1 ∧
    corridorState owner.1.1.1.1.1 owner.1.1.1.1.2
        (repeated.prefixTrace.schedule.get repeated.pair.1) =
      corridorState owner.1.1.1.1.1 owner.1.1.1.1.2
        (repeated.prefixTrace.schedule.get repeated.pair.2)
  have earlierVal :
      (repeated.prefixTrace.schedule.get repeated.pair.1).1 =
        repeated.pair.1.1 := by
    have fromPrefix := congrArg (fun stage => stage.1)
      (repeated.prefix_get_eq_original_get repeated.pair.1)
    calc
      (repeated.prefixTrace.schedule.get repeated.pair.1).1 =
          ((family.traceAt owner.1.1.1).schedule.get
            (repeated.originalIndex repeated.pair.1)).1 := fromPrefix
      _ = (repeated.originalIndex repeated.pair.1).1 := by
        exact traceGetVal (repeated.originalIndex repeated.pair.1)
      _ = repeated.pair.1.1 := rfl
  have laterVal :
      (repeated.prefixTrace.schedule.get repeated.pair.2).1 =
        repeated.pair.2.1 := by
    have fromPrefix := congrArg (fun stage => stage.1)
      (repeated.prefix_get_eq_original_get repeated.pair.2)
    calc
      (repeated.prefixTrace.schedule.get repeated.pair.2).1 =
          ((family.traceAt owner.1.1.1).schedule.get
            (repeated.originalIndex repeated.pair.2)).1 := fromPrefix
      _ = (repeated.originalIndex repeated.pair.2).1 := by
        exact traceGetVal (repeated.originalIndex repeated.pair.2)
      _ = repeated.pair.2.1 := rfl
  constructor
  · rw [earlierVal, laterVal]
    exact repeated.ordered
  · have equal := repeated.equal
    rw [repeated.state_eq] at equal
    rw [← traceState]
    change (family.traceAt owner.1.1.1).state
        (repeated.prefixTrace.schedule.get repeated.pair.1) =
      (family.traceAt owner.1.1.1).state
        (repeated.prefixTrace.schedule.get repeated.pair.2)
    exact equal

/-- Exact response system on the dependent representative functions and the
complete owner/context schedule. -/
noncomputable def canonicalF5ResponseSystem
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate)) :
    Core.Response.System (CanonicalColdRepresentative profile) :=
  Core.Response.System.ofDecodedContexts
    (CanonicalColdContext profile) (CanonicalColdContext profile) Bool
    (fun representative context =>
      germTargetResponse context.1.1.1.1 context.1.1.1.2
        Target decideTarget (representative context.1))
    id

/-- CT7's G1/G2/G3 specification over the active view of the literal cold
ledger.  Realization is restricted to an owner selected by the exact stored
F5 partition in that same view; terminal and repeated bounded outcomes are
both ordinary representatives of this one partition. -/
noncomputable def canonicalF5CT7Spec
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    _root_.Hypostructure.CT7.Spec
      (Core.Residual.Focus.ActiveView
        (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
          cycleLengthDecidable Target decideTarget handoffItems handoffSupport)) where
  Representative := CanonicalColdRepresentative profile
  system := canonicalF5ResponseSystem profile Target decideTarget
  Realizes := fun view representative context =>
    let family := CanonicalColdFamily profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    ∃ selected :
        Core.Finite.ColdCorridor.Contract.Classification.IsFailure
          (family.contractAt context.1.1)
          ((family.storedClassificationQuery.read view.previous).classify
            context.1) .f5,
      letI : DecidableEq object.Vertex := object.vertices.decEq
      Graph.HasCycleWithLength CycleLengthOK
        (object.induce
          ((returnPrefixSupport context.1.1.1.1 context.1.1.1.2
            (representative context.1)).toFinset ∪
            (returnPrefixSupport context.1.1.1.1 context.1.1.1.2
              (germStage context.1.1.1.1 context.1.1.1.2)).toFinset))

/-- CT7 capability read from the exact active view.  Both representatives and
the complete coordinate schedule are ordinary queries on that view. -/
noncomputable def canonicalF5CT7Capability
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    _root_.Hypostructure.CT7.Capability
      (canonicalF5CT7Spec (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) := by
  let focus := canonicalF5Focus (Previous := Previous) profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  let representatives : Core.Residual.Query
      (Core.Residual.Focus.ActiveView focus)
      (fun _ => Core.Response.Representatives
        (CanonicalColdRepresentative profile)) :=
    (Core.Residual.Focus.ActiveQuery.ofFunction
      (profile := focus) fun stage active =>
        canonicalF5Representatives profile CycleLengthOK cycleLengthDecidable
          Target decideTarget handoffItems handoffSupport
          (Core.Residual.Focus.ActiveView.of stage active)).onView
  let contexts : Core.Residual.Query
      (Core.Residual.Focus.ActiveView focus)
      (fun _ => Enumeration (CanonicalColdContext profile)) :=
    Core.Residual.Query.ofFunction fun _ => canonicalColdContextSchedule profile
  exact _root_.Hypostructure.CT7.Capability.ofExactContexts
    representatives contexts
    (by change DecidableEq Bool; infer_instance)
    (fun _view _coordinate => Classical.propDecidable _)
    (by
      intro _view context
      change CanonicalColdContext profile at context
      have member : context ∈ (canonicalColdContextSchedule profile).values := by
        unfold canonicalColdContextSchedule
        rw [Core.Finite.DependentEnumeration.mem_flatten_values]
        constructor
        · exact Enumeration.mem_attach_values _ context.1
        · exact Enumeration.mem_ofFinEnum_values inferInstance context.2
      obtain ⟨index, equal⟩ :=
        ((canonicalColdContextSchedule profile).mem_iff_exists_index context).mp member
      exact ⟨index, equal.symm⟩)

/-- Exact CT7 work reindexed from active views to classified cold stages.
Inactive stages have no CT7 payload. -/
noncomputable def canonicalF5PayloadBudget
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    Core.PolynomialCheckBudget
      ((CanonicalColdFamily profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous) := by
  let focus := canonicalF5Focus (Previous := Previous) profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  let capability := canonicalF5CT7Capability (Previous := Previous) profile
    CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  let activeBudget := _root_.Hypostructure.CT7.generationBudget capability
  exact
    { size := fun stage =>
        match (focus.select stage).value with
        | .isTrue active =>
            activeBudget.size (Core.Residual.Focus.ActiveView.of stage active)
        | .isFalse _ => 0
      checks := fun stage =>
        match (focus.select stage).value with
        | .isTrue active =>
            activeBudget.checks (Core.Residual.Focus.ActiveView.of stage active)
        | .isFalse _ => 0
      coefficient := activeBudget.coefficient
      degree := activeBudget.degree
      bounded := by
        intro stage
        cases selected : (focus.select stage).value with
        | isTrue active =>
            exact activeBudget.bounded
              (Core.Residual.Focus.ActiveView.of stage active)
        | isFalse _ => simp }

/-- The focused CT7 output stored in the cold ledger. -/
abbrev CanonicalF5CT7Output
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : (CanonicalColdFamily profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous)
    (active : (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport).Active stage) :=
  _root_.Hypostructure.CT7.Generated
    (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
    (Core.Residual.Focus.ActiveView.of stage active)

/-- Append the actual CT7 G1/G2/G3 payload to the literal classified cold
stage.  This is the public residual-native F5 execution. -/
noncomputable def runCanonicalF5CT7
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : (CanonicalColdFamily profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous) :
    Core.Counted (Core.Residual.Focus.Stage
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
      (CanonicalF5CT7Output profile CycleLengthOK cycleLengthDecidable
        Target decideTarget handoffItems handoffSupport)) := by
  let focus := canonicalF5Focus (Previous := Previous) profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  let capability := canonicalF5CT7Capability (Previous := Previous) profile
    CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  let payloadBudget := canonicalF5PayloadBudget (Previous := Previous) profile
    CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  refine Core.Residual.Focus.runCountedPayload focus payloadBudget stage
    (fun active _selectionChecks _selectionExact =>
      _root_.Hypostructure.CT7.generateCounted capability
        (Core.Residual.Focus.ActiveView.of stage active)) ?_
  intro active _selectionChecks _selectionExact
  unfold payloadBudget canonicalF5PayloadBudget
  cases selected : (focus.select stage).value with
  | isTrue selectedActive =>
      have equal : selectedActive = active := Subsingleton.elim _ _
      cases equal
      change _ = match (focus.select stage).value with
        | .isTrue selectedActive =>
            (_root_.Hypostructure.CT7.generateCounted capability
              (Core.Residual.Focus.ActiveView.of stage selectedActive)).checks
        | .isFalse _ => 0
      rw [selected]
  | isFalse absent => exact (absent active).elim

@[simp] theorem runCanonicalF5CT7_previous
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (stage : (CanonicalColdFamily profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport).ClassifiedStateStage Previous) :
    (runCanonicalF5CT7 profile CycleLengthOK cycleLengthDecidable Target
      decideTarget handoffItems handoffSupport stage).value.previous = stage := by
  unfold runCanonicalF5CT7
  exact Core.Residual.Focus.runCountedPayload_previous _ _ _ _ _

/-- Focus inherited by successors of the exact CT7 ledger extension. -/
noncomputable abbrev CanonicalF5CT7SuccessorFocus
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :=
  Core.Residual.Focus.successor
    (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
    (CanonicalF5CT7Output profile CycleLengthOK cycleLengthDecidable
      Target decideTarget handoffItems handoffSupport)

/-- Read the actual CT7 payload from the newest focused ledger entry. -/
noncomputable def canonicalF5CT7OutputQuery
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex) :
    Core.Residual.Focus.ActiveQuery
      (CanonicalF5CT7SuccessorFocus (Previous := Previous) profile
        CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
      (fun stage active => CanonicalF5CT7Output profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
        stage.previous active) :=
  Core.Residual.Focus.ActiveQuery.latest

/-- G1 closes from the realization certificate produced by CT7 on the exact
active view.  The induced-cycle certificate is transported through the
canonical induced embedding into the ambient graph. -/
theorem canonicalF5G1Target
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (certificate : _root_.Hypostructure.CT7.RealizationCertificate
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) view) :
    Graph.HasCycleWithLength CycleLengthOK object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let representatives : Core.Response.Representatives
      (CanonicalColdRepresentative profile) :=
    (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport).representativesAt view
  let context : CanonicalColdContext profile := certificate.context
  let support : Finset object.Vertex :=
    (returnPrefixSupport context.1.1.1.1 context.1.1.1.2
      (representatives.source context.1)).toFinset ∪
      (returnPrefixSupport context.1.1.1.1 context.1.1.1.2
        (germStage context.1.1.1.1 context.1.1.1.2)).toFinset
  have realized :
      (canonicalF5CT7Spec (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport).Realizes
          view representatives.source context := by
    simpa [representatives, context] using certificate.realizes
  unfold canonicalF5CT7Spec at realized
  change ∃ _selected,
    Graph.HasCycleWithLength CycleLengthOK (object.induce support) at realized
  rcases realized with ⟨_selected, ⟨cycle⟩⟩
  exact ⟨cycle.mapHom (object.induceEmbedding support).toHom
    (object.induceEmbedding support).injective⟩

/-- The standard disjunctive-target adapter for G1.  The left disjunct is
the exact ambient cycle reconstructed from CT7's stored realization; the
right disjunct is completely parametric and is neither inspected nor
decided. -/
theorem canonicalF5G1DisjunctiveTarget
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (certificate : _root_.Hypostructure.CT7.RealizationCertificate
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) view)
    (Rest : FiniteObject.{u} → Prop) :
    Graph.HasCycleWithLength CycleLengthOK object ∨ Rest object :=
  Or.inl (canonicalF5G1Target profile CycleLengthOK cycleLengthDecidable
    Target decideTarget handoffItems handoffSupport view certificate)

/-- G2 is the exact target defect selected by CT7.  The two pieces are the
stored replacement/source stages for the selected owner and the context is
CT7's scheduled distinguishing context. -/
theorem canonicalF5G2Defect
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (residual : _root_.Hypostructure.CT7.DistinguishingResidual
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) view) :
    let owner := residual.context.1
    let representatives :=
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
        |>.representativesAt view
    F2TargetDefect owner.1.1.1 owner.1.1.2 Target
      (representatives.replacement owner)
      (representatives.source owner) := by
  dsimp only
  apply f2TargetDefect_of_response_ne
    (Target := Target) (decideTarget := decideTarget)
  have different := residual.contextDiffers
  simpa [canonicalF5CT7Spec, canonicalF5ResponseSystem,
    Core.Response.System.ofDecodedContexts] using different.symm

/-- G3 is the universal exact-response equality generated by CT7, projected
pointwise to every exact F5 owner/context coordinate in the active residual.
No response is recomputed by this theorem. -/
theorem canonicalF5G3Neutral
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (certificate : _root_.Hypostructure.CT7.NeutralityCertificate
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) view) :
    ∀ context : CanonicalColdContext profile,
      let representatives : Core.Response.Representatives
          (CanonicalColdRepresentative profile) :=
        (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
          cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
          |>.representativesAt view
      germTargetResponse context.1.1.1.1 context.1.1.1.2 Target decideTarget
          (representatives.source context.1) =
        germTargetResponse context.1.1.1.1 context.1.1.1.2
          Target decideTarget (representatives.replacement context.1) := by
  intro context
  simpa [canonicalF5CT7Spec, canonicalF5ResponseSystem,
    Core.Response.System.ofDecodedContexts] using
      certificate.universal.equalInContext context

/-- G3 data for one repeated cold owner, recovered entirely from the active
CT7 payload and the repeated-F5 query on its incoming ledger.  The shorter
orientation, equal interface state, and all-context response equality refer
to the same two stored representatives. -/
theorem canonicalF5G3RepeatedFacts
    {Previous : Type*}
    {object : FiniteObject.{u}} {order : Nat}
    (profile : InducedPathMaximalPacking.Profile object order)
    (CycleLengthOK : Nat → Prop)
    (cycleLengthDecidable : DecidablePred CycleLengthOK)
    (Target : FiniteObject.{u} → Prop)
    (decideTarget : ∀ candidate, Decidable (Target candidate))
    {Handoff : Type u}
    (handoffItems : Enumeration Handoff)
    (handoffSupport : Handoff → Finset object.Vertex)
    (view : Core.Residual.Focus.ActiveView
      (canonicalF5Focus (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport))
    (certificate : _root_.Hypostructure.CT7.NeutralityCertificate
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport) view)
    (owner :
      let family := CanonicalColdFamily profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport
      family.RepeatedF5Owner (family.classifiedStateQuery.read view.previous)) :
    let representatives : Core.Response.Representatives
        (CanonicalColdRepresentative profile) :=
      (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
        cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
        |>.representativesAt view
    (representatives.replacement owner.1.1).val <
        (representatives.source owner.1.1).val ∧
      corridorState owner.1.1.1.1.1 owner.1.1.1.1.2
          (representatives.replacement owner.1.1) =
        corridorState owner.1.1.1.1.1 owner.1.1.1.1.2
          (representatives.source owner.1.1) ∧
      germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2 Target decideTarget
          (representatives.source owner.1.1) =
        germTargetResponse owner.1.1.1.1.1 owner.1.1.1.1.2
          Target decideTarget (representatives.replacement owner.1.1) := by
  dsimp only
  let family := CanonicalColdFamily profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport
  letI := family.stateFintype owner.1.1.1
  let repeated := family.storedRepeatedF5Witness view.previous owner
  have representativeEq := canonicalF5Representatives_at_repeated profile
    CycleLengthOK cycleLengthDecidable Target decideTarget handoffItems handoffSupport
    view owner
  have storedFacts := canonicalRepeatedF5Witness_facts profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport view owner
  have allContexts := canonicalF5G3Neutral profile CycleLengthOK
    cycleLengthDecidable Target decideTarget handoffItems handoffSupport view certificate
  let representatives : Core.Response.Representatives
      (CanonicalColdRepresentative profile) :=
    (canonicalF5CT7Capability (Previous := Previous) profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport)
      |>.representativesAt view
  have sourceEq : representatives.source owner.1.1 =
      repeated.prefixTrace.schedule.get repeated.pair.2 := by
    change (canonicalF5Representatives profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport view).source
        owner.1.1 = repeated.prefixTrace.schedule.get repeated.pair.2
    exact representativeEq.1
  have replacementEq : representatives.replacement owner.1.1 =
      repeated.prefixTrace.schedule.get repeated.pair.1 := by
    change (canonicalF5Representatives profile CycleLengthOK
      cycleLengthDecidable Target decideTarget handoffItems handoffSupport view).replacement
        owner.1.1 = repeated.prefixTrace.schedule.get repeated.pair.1
    exact representativeEq.2
  refine ⟨?_, ?_, ?_⟩
  · rw [replacementEq, sourceEq]
    exact storedFacts.1
  · rw [replacementEq, sourceEq]
    exact storedFacts.2
  · exact allContexts ⟨owner.1.1, Sum.inl 0⟩

/-! Build the reusable Core producer directly from the literal corridor
schedule and a residual-owned finite state observation.  Core derives all
bound constants and the F5 schedule from this producer. -/
noncomputable def FirstFailurePresentation.coreProducer
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    Core.Finite.ColdCorridor.Producer Item State :=
  Core.Finite.ColdCorridor.Producer.ofObservation
    { schedule := corridor.items
      state := corridor.state }
    corridor.observation

/-! When the corridor item type itself has a `FinEnum`, the schedule is
constructed by Core from that finite type.  This adapter deliberately has no
schedule argument, so an application cannot smuggle in a selected list or an
ordering unrelated to the residual-owned finite family. -/
noncomputable def FirstFailurePresentation.coreCompleteProducer
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [FinEnum Item] [Fintype State]
    {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    (schedule_complete : corridor.items.values =
      @FinEnum.toList Item inferInstance) :
    Core.Finite.ColdCorridor.Producer Item State :=
  Core.Finite.ColdCorridor.Producer.ofObservation
    (Core.Finite.ColdCorridor.Contract.CompleteStateTrace.toStateTrace
      { state := corridor.state })
    corridor.observation

/-! Public projections for the complete Core-owned corridor result.  These
projections preserve the producer's dependent event types, so the caller can
read the first-hit/F5 classification and derived budgets without introducing
a second classifier or arithmetic layer. -/
noncomputable def FirstFailurePresentation.producer
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    Core.Finite.ColdCorridor.Producer Item State :=
  presentation.coreProducer

noncomputable def FirstFailurePresentation.classificationFromState
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    Core.Finite.ColdCorridor.Contract.Classification
      presentation.producer.contract :=
  presentation.producer.contract.classification

noncomputable def FirstFailurePresentation.f5ScheduleFromState
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    Enumeration
      {item : Item //
        presentation.producer.f5 item
          (presentation.producer.run item)} :=
  presentation.producer.f5Schedule

/-! The bounded terminal/repeated-state alternative is computed from the
literal public state trace. -/
noncomputable def FirstFailurePresentation.boundedOutcome
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    Core.Finite.ColdCorridor.Contract.StateTrace.BoundedOutcome
      presentation.producer.trace :=
  presentation.producer.trace.boundedOutcome

/-! The canonical bounded-germ candidate schedule is exactly Core's F5
subschedule.  Its support is read from the corresponding graph stage. -/
abbrev FirstFailurePresentation.Germ
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :=
  {item : Item // presentation.producer.f5 item
    (presentation.producer.run item)}

noncomputable def FirstFailurePresentation.germSchedule
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    Enumeration presentation.Germ :=
  presentation.producer.f5Schedule

noncomputable def FirstFailurePresentation.germSupport
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    (germ : presentation.Germ) : Finset object.Vertex :=
  (corridor.stages germ.1).toFinset

noncomputable def FirstFailurePresentation.vertexSchedule
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (_presentation : FirstFailurePresentation object Item State corridor) :
    Enumeration object.Vertex :=
  Enumeration.ofFinEnum object.vertices

theorem FirstFailurePresentation.germSupport_vertices
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    (germ : presentation.Germ)
    (_member : germ ∈ presentation.germSchedule.values) :
    presentation.germSupport germ ⊆ presentation.vertexSchedule.toFinset := by
  intro vertex _vertex_mem
  apply (Enumeration.mem_toFinset presentation.vertexSchedule vertex).mpr
  exact Enumeration.mem_ofFinEnum_values object.vertices vertex

def FirstFailurePresentation.qCold
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (_presentation : FirstFailurePresentation object Item State corridor) : Nat :=
  Fintype.card State

noncomputable def FirstFailurePresentation.mCold
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) : Nat :=
  Core.Finite.ColdCorridor.supportSizeBound
    presentation.germSchedule presentation.germSupport

noncomputable def FirstFailurePresentation.bCold
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) : Nat :=
  Core.Finite.ColdCorridor.overlapBound
    presentation.germSchedule presentation.vertexSchedule
    presentation.germSupport

noncomputable def FirstFailurePresentation.dCold
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) : Nat :=
  presentation.mCold * presentation.bCold + 1

noncomputable def FirstFailurePresentation.germPacking
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :=
  Core.Finite.ColdCorridor.supportPacking
    presentation.germSchedule presentation.germSupport

theorem FirstFailurePresentation.germPacking_pairwise_disjoint
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    {left right : presentation.Germ}
    (left_mem : left ∈ presentation.germPacking.selected)
    (right_mem : right ∈ presentation.germPacking.selected)
    (different : left ≠ right) :
    Disjoint (presentation.germSupport left)
      (presentation.germSupport right) :=
  Core.Finite.ColdCorridor.supportPacking_pairwise_disjoint
    presentation.germSchedule presentation.germSupport
    left_mem right_mem different

theorem FirstFailurePresentation.germPacking_card_bound
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor) :
    presentation.germSchedule.card ≤
      presentation.germPacking.selected.length * presentation.dCold := by
  exact Core.Finite.ColdCorridor.supportPacking_card_bound
    presentation.germSchedule presentation.vertexSchedule
    presentation.germSupport presentation.germSupport_vertices

theorem FirstFailurePresentation.germSchedule_nonempty_of_f5
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    (classified : presentation.producer.contract.classify =
      Core.Finite.ColdCorridor.Failure.f5) :
    presentation.germSchedule.values ≠ [] := by
  have allF5 :=
    presentation.producer.contract.all_f5_of_classify_eq_f5 classified
  obtain ⟨item, item_mem⟩ :=
    List.exists_mem_of_ne_nil corridor.items.values corridor.items_nonempty
  exact presentation.producer.f5Schedule_nonempty
    ⟨item, item_mem, allF5 item item_mem⟩

theorem FirstFailurePresentation.germPacking_nonempty_of_f5
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    (classified : presentation.producer.contract.classify =
      Core.Finite.ColdCorridor.Failure.f5) :
    presentation.germPacking.selected ≠ [] := by
  exact Core.Finite.ColdCorridor.supportPacking_selected_nonempty
    presentation.germSchedule presentation.germSupport
    (presentation.germSchedule_nonempty_of_f5 classified)

noncomputable def FirstFailurePresentation.boundsFromState
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    (Interface : Type u) [Fintype Interface]
    {Vertex : Type u}
    (vertices : Enumeration Vertex)
    (support : Item → Finset Vertex) :
    Core.Finite.ColdCorridor.Contract.StateBounds State :=
  presentation.producer.boundsOfFiniteInterfaceAndSupport
    Interface vertices support

noncomputable def FirstFailurePresentation.classificationStage
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    {Previous : Type u}
    (previous : Previous) :
    Core.Finite.ColdCorridor.Producer.ClassificationStage Previous
      presentation.producer :=
  Core.Finite.ColdCorridor.Producer.classifyIntoLedger
    presentation.producer previous

noncomputable def FirstFailurePresentation.classificationQuery
    {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] {corridor : Corridor object Item State}
    (presentation : FirstFailurePresentation object Item State corridor)
    {Previous : Type u} :
    Core.Residual.Query
      (Core.Finite.ColdCorridor.Producer.ClassificationStage Previous
        presentation.producer)
      (fun _ =>
        (Core.Finite.ColdCorridor.Producer.contract
          presentation.producer).Classification) :=
  Core.Finite.ColdCorridor.Producer.classificationQuery
    presentation.producer

def corridorEvents {object : FiniteObject.{u}} {Item : Type uItem} {State : Type uState}
    [Fintype State] (corridor : Corridor object Item State) :
    Core.Finite.ScheduleEvents.Contract Item where
  schedule := corridor.items
  Output := fun _item => Enumeration object.Vertex
  run := corridor.stages

/-! ## Focused corridor execution surface -/

/-- Build the Core schedule-event executor for a graph corridor whose graph
object and stage producer are read from the active residual.  Graph supplies
only graph-typed stage outputs; Core owns the schedule scan, hit/no-hit split,
and downstream routing. -/
def focusedCorridorEvents {Previous : Type u}
    {focus : _root_.Hypostructure.Core.Residual.Focus.Profile Previous}
    (object :
      _root_.Hypostructure.Core.Residual.Focus.ActiveQuery focus
        fun _previous _active => FiniteObject.{u})
    (Item : Type u)
    (items :
      _root_.Hypostructure.Core.Residual.Focus.ActiveQuery focus
        fun _previous _active => Enumeration Item)
    (stages :
      _root_.Hypostructure.Core.Residual.Focus.ActiveQuery focus
        fun previous active =>
          (item : Item) -> Enumeration ((object.read previous active).Vertex))
    (event : (previous : Previous) -> (active : focus.Active previous) ->
      (item : Item) -> Enumeration ((object.read previous active).Vertex) ->
        Prop)
    (eventDecidable :
      (previous : Previous) -> (active : focus.Active previous) ->
        (item : Item) ->
          Decidable (event previous active item
            ((stages.read previous active) item))) :
    Core.Finite.ScheduleEvents.FocusedContract focus :=
  Core.Finite.ScheduleEvents.focusedFromQueries Item items
    (fun previous active _item =>
      Enumeration ((object.read previous active).Vertex))
    stages event eventDecidable

end Hypostructure.Graph.InducedPathCold

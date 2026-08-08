import Hypostructure.Graph.WindowJoinIdentity

/-!
# The ordinary deficiency reserve

This file gives the two finite carrier families used by
`def:typeB-ledger-carriers`' ordinary reserve.  A positive-deficiency unit is
indexed by both its support vertex and its local unit number, so repeated units
at one vertex remain distinct.  A window-boundary unit is the existing ordered
remainder-to-window incidence, restricted to a declared support by its
remainder endpoint.  The final carrier is their tagged disjoint union.

There is no strategy state, residual wrapper, choice function, or capacity-token
ledger here.  All counts are the counts of these literal finite families.
-/

namespace Hypostructure.Graph

open Hypostructure

universe u v

variable {object : FiniteObject.{u}}

noncomputable section

local instance (priority := low) {α : Type v} : DecidableEq α :=
  Classical.decEq α

namespace OrdinaryDeficiencyReserve

/-- One unit of positive deficiency at a support vertex.  The natural index is
strictly below that vertex's deficiency when the unit belongs to the schedule. -/
abbrev PositiveDeficiencyUnit (object : FiniteObject.{u}) := object.Vertex × Nat

/-- One support-local incidence from the remainder side to the packed-window
side.  This is the same ordered pair used by `windowRemainderIncidences`. -/
abbrev WindowBoundaryUnit (object : FiniteObject.{u}) :=
  object.Vertex × object.Vertex

/-- The ordinary reserve carrier universe.  The tag makes deficiency units and
window-boundary units disjoint even when their vertex data coincide. -/
abbrev Carrier (object : FiniteObject.{u}) :=
  PositiveDeficiencyUnit object ⊕ WindowBoundaryUnit object

/-- The support-side vertex owning a tagged ordinary-reserve unit. -/
def anchor (carrier : Carrier object) : object.Vertex :=
  match carrier with
  | .inl deficiency => deficiency.1
  | .inr incidence => incidence.1

/-- The literal subfamily of a reserve anchored in a finite vertex support. -/
noncomputable def anchorFibre (reserve : Finset (Carrier object))
    (support : Finset object.Vertex) : Finset (Carrier object) := by
  classical
  exact reserve.filter fun carrier => anchor carrier ∈ support

/-- The literal fibre over one anchor. -/
noncomputable def anchorFibreAt (reserve : Finset (Carrier object))
    (vertex : object.Vertex) : Finset (Carrier object) := by
  classical
  exact reserve.filter fun carrier => anchor carrier = vertex

theorem mem_anchorFibre_iff {reserve : Finset (Carrier object)}
    {support : Finset object.Vertex} {carrier : Carrier object} :
    carrier ∈ anchorFibre reserve support ↔
      carrier ∈ reserve ∧ anchor carrier ∈ support := by
  classical
  simp [anchorFibre]

theorem mem_anchorFibreAt_iff {reserve : Finset (Carrier object)}
    {vertex : object.Vertex} {carrier : Carrier object} :
    carrier ∈ anchorFibreAt reserve vertex ↔
      carrier ∈ reserve ∧ anchor carrier = vertex := by
  classical
  simp [anchorFibreAt]

theorem anchorFibre_subset (reserve : Finset (Carrier object))
    (support : Finset object.Vertex) :
    anchorFibre reserve support ⊆ reserve := by
  exact Finset.filter_subset _ _

theorem anchorFibreAt_disjoint {reserve : Finset (Carrier object)}
    {left right : object.Vertex} (distinct : left ≠ right) :
    Disjoint (anchorFibreAt reserve left) (anchorFibreAt reserve right) := by
  classical
  rw [Finset.disjoint_left]
  intro carrier leftMember rightMember
  have leftAnchor := (mem_anchorFibreAt_iff.mp leftMember).2
  have rightAnchor := (mem_anchorFibreAt_iff.mp rightMember).2
  exact distinct (leftAnchor.symm.trans rightAnchor)

theorem anchorFibre_disjoint {reserve : Finset (Carrier object)}
    {left right : Finset object.Vertex} (disjoint : Disjoint left right) :
    Disjoint (anchorFibre reserve left) (anchorFibre reserve right) := by
  classical
  rw [Finset.disjoint_left]
  intro carrier leftMember rightMember
  exact (Finset.disjoint_left.mp disjoint)
    (mem_anchorFibre_iff.mp leftMember).2
    (mem_anchorFibre_iff.mp rightMember).2

theorem anchorFibre_eq_biUnion_anchorFibreAt
    (reserve : Finset (Carrier object)) (support : Finset object.Vertex) :
    anchorFibre reserve support =
      support.biUnion fun vertex => anchorFibreAt reserve vertex := by
  classical
  ext carrier
  simp [anchorFibre, anchorFibreAt, and_comm]

theorem anchorFibre_biUnion {Index : Type*} [DecidableEq Index]
    (reserve : Finset (Carrier object)) (indices : Finset Index)
    (supports : Index → Finset object.Vertex) :
    anchorFibre reserve (indices.biUnion supports) =
      indices.biUnion fun index => anchorFibre reserve (supports index) := by
  classical
  ext carrier
  simp only [mem_anchorFibre_iff, Finset.mem_biUnion]
  constructor
  · rintro ⟨carrierMem, index, indexMem, anchorMem⟩
    exact ⟨index, indexMem, carrierMem, anchorMem⟩
  · rintro ⟨index, indexMem, carrierMem, anchorMem⟩
    exact ⟨carrierMem, index, indexMem, anchorMem⟩

theorem anchorFibre_eq_self_iff
    (reserve : Finset (Carrier object)) (support : Finset object.Vertex) :
    anchorFibre reserve support = reserve ↔
      ∀ carrier ∈ reserve, anchor carrier ∈ support := by
  classical
  rw [anchorFibre, Finset.filter_eq_self]

end OrdinaryDeficiencyReserve

open OrdinaryDeficiencyReserve

namespace FiniteObject

/-- The literal indexed units
`(y,j)`, `y ∈ X`, `j < δ - d_X(y)`. -/
noncomputable def positiveDeficiencyUnits (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    Finset (PositiveDeficiencyUnit object) := by
  classical
  exact support.biUnion fun vertex =>
    (Finset.range (threshold - object.internalDegree support vertex)).image
      fun index => (vertex, index)

theorem mem_positiveDeficiencyUnits_iff
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (unit : PositiveDeficiencyUnit object) :
    unit ∈ object.positiveDeficiencyUnits support threshold ↔
      unit.1 ∈ support ∧
        unit.2 < threshold - object.internalDegree support unit.1 := by
  classical
  simp only [positiveDeficiencyUnits, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨vertex, vertexMem, index, indexMem, rfl⟩
    exact ⟨vertexMem, indexMem⟩
  · rintro ⟨vertexMem, indexMem⟩
    exact ⟨unit.1, vertexMem, unit.2, indexMem, rfl⟩

/-- The indexed schedule preserves multiplicity exactly. -/
theorem card_positiveDeficiencyUnits (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    (object.positiveDeficiencyUnits support threshold).card =
      object.positiveDeficiency support threshold := by
  classical
  rw [positiveDeficiencyUnits, Finset.card_biUnion]
  · rw [Hypostructure.Graph.FiniteObject.positiveDeficiency]
    refine Finset.sum_congr rfl ?_
    intro vertex _member
    rw [Finset.card_image_of_injective _ (fun _ _ equality =>
      congrArg Prod.snd equality), Finset.card_range]
  · intro left _leftMem right _rightMem distinct
    change Disjoint
      ((Finset.range (threshold - object.internalDegree support left)).image
        fun index => (left, index))
      ((Finset.range (threshold - object.internalDegree support right)).image
        fun index => (right, index))
    rw [Finset.disjoint_left]
    intro unit leftMember rightMember
    obtain ⟨leftIndex, _leftIndexMem, leftEq⟩ := Finset.mem_image.mp leftMember
    obtain ⟨rightIndex, _rightIndexMem, rightEq⟩ := Finset.mem_image.mp rightMember
    apply distinct
    exact (congrArg Prod.fst leftEq).trans (congrArg Prod.fst rightEq).symm

/-- The existing remainder-to-window incidence family restricted to a finite
support by its remainder endpoint. -/
noncomputable def localWindowBoundaryIncidences (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) : Finset (WindowBoundaryUnit object) := by
  classical
  exact (object.windowRemainderIncidences packing).filter
    fun incidence => incidence.1 ∈ support

theorem mem_localWindowBoundaryIncidences_iff
    (object : FiniteObject.{u}) (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) (incidence : WindowBoundaryUnit object) :
    incidence ∈ object.localWindowBoundaryIncidences packing support ↔
      incidence.1 ∈ support ∧ object.graph.Adj incidence.1 incidence.2 ∧
        incidence.1 ∈ object.remainderSupport packing ∧
        incidence.2 ∈ object.windowSupport packing := by
  classical
  rw [localWindowBoundaryIncidences, Finset.mem_filter,
    object.mem_windowRemainderIncidences_iff packing incidence]
  constructor
  · rintro ⟨⟨adjacent, remainder, window⟩, insideSupport⟩
    exact ⟨insideSupport, adjacent, remainder, window⟩
  · rintro ⟨insideSupport, adjacent, remainder, window⟩
    exact ⟨⟨adjacent, remainder, window⟩, insideSupport⟩

theorem localWindowBoundaryIncidences_subset
    (object : FiniteObject.{u}) (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) :
    object.localWindowBoundaryIncidences packing support ⊆
      object.windowRemainderIncidences packing := by
  exact Finset.filter_subset _ _

/-- Restricting the cut family to the whole remainder changes nothing. -/
theorem localWindowBoundaryIncidences_remainderSupport
    (object : FiniteObject.{u}) (packing : Finset (Finset object.Vertex)) :
    object.localWindowBoundaryIncidences packing
        (object.remainderSupport packing) =
      object.windowRemainderIncidences packing := by
  classical
  apply Finset.filter_eq_self.2
  intro incidence member
  exact (object.mem_windowRemainderIncidences_iff packing incidence).1 member |>.2.1

/-- The two tagged summands of the ordinary reserve. -/
noncomputable def deficiencyCarriers (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat) :
    Finset (Carrier object) := by
  classical
  exact (object.positiveDeficiencyUnits support threshold).image Sum.inl

noncomputable def windowBoundaryCarriers (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) : Finset (Carrier object) := by
  classical
  exact (object.localWindowBoundaryIncidences packing support).image Sum.inr

/-- The tagged ordinary deficiency reserve. -/
noncomputable def ordinaryDeficiencyReserve (object : FiniteObject.{u})
    (threshold : Nat) (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) : Finset (Carrier object) := by
  exact object.deficiencyCarriers support threshold ∪
    object.windowBoundaryCarriers packing support

theorem deficiencyCarriers_disjoint_windowBoundaryCarriers
    (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) :
    Disjoint (object.deficiencyCarriers support threshold)
      (object.windowBoundaryCarriers packing support) := by
  classical
  rw [Finset.disjoint_left]
  intro carrier deficiencyMember boundaryMember
  obtain ⟨unit, _unitMember, rfl⟩ := Finset.mem_image.mp deficiencyMember
  simp [windowBoundaryCarriers] at boundaryMember

theorem mem_ordinaryDeficiencyReserve_iff
    (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) (carrier : Carrier object) :
    carrier ∈ object.ordinaryDeficiencyReserve threshold packing support ↔
      carrier ∈ object.deficiencyCarriers support threshold ∨
        carrier ∈ object.windowBoundaryCarriers packing support := by
  rw [ordinaryDeficiencyReserve, Finset.mem_union]

/-- Exact disjoint-union count of the two reserve families. -/
theorem card_ordinaryDeficiencyReserve
    (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    (support : Finset object.Vertex) :
    (object.ordinaryDeficiencyReserve threshold packing support).card =
      object.positiveDeficiency support threshold +
        (object.localWindowBoundaryIncidences packing support).card := by
  classical
  rw [ordinaryDeficiencyReserve,
    Finset.card_union_of_disjoint
      (object.deficiencyCarriers_disjoint_windowBoundaryCarriers threshold packing support),
    deficiencyCarriers, windowBoundaryCarriers,
    Finset.card_image_of_injective _ (fun _ _ equality => Sum.inl.inj equality),
    Finset.card_image_of_injective _ (fun _ _ equality => Sum.inr.inj equality),
    object.card_positiveDeficiencyUnits support threshold]

/-- On the whole remainder the local boundary summand is exactly the cut
incidence count, hence exactly its boundary incidence. -/
theorem card_ordinaryDeficiencyReserve_remainderSupport
    (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex)) :
    (object.ordinaryDeficiencyReserve threshold packing
        (object.remainderSupport packing)).card =
      object.positiveDeficiency (object.remainderSupport packing) threshold +
        object.boundaryIncidence (object.remainderSupport packing) := by
  rw [object.card_ordinaryDeficiencyReserve threshold packing,
    object.localWindowBoundaryIncidences_remainderSupport packing,
    object.card_windowRemainderIncidences packing]

/-- The deficiency summand refines the boundary supply on the standing
baseline, with no choice of units: this is the cardinal form of
`def⁺(R) ≤ e(R,W)`. -/
theorem card_positiveDeficiencyUnits_le_windowBoundaryUnits
    (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.positiveDeficiencyUnits (object.remainderSupport packing) threshold).card ≤
      (object.localWindowBoundaryIncidences packing
        (object.remainderSupport packing)).card := by
  rw [object.card_positiveDeficiencyUnits,
    object.localWindowBoundaryIncidences_remainderSupport packing,
    object.card_windowRemainderIncidences packing]
  exact object.positiveDeficiency_le_boundaryIncidence
    (object.remainderSupport packing) threshold baseline

/-- Consequently the full ordinary reserve uses at most two tagged units per
remainder-to-window incidence. -/
theorem card_ordinaryDeficiencyReserve_le_two_mul_windowBoundary
    (object : FiniteObject.{u}) (threshold : Nat)
    (packing : Finset (Finset object.Vertex))
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.ordinaryDeficiencyReserve threshold packing
        (object.remainderSupport packing)).card ≤
      2 * (object.windowRemainderIncidences packing).card := by
  have deficiency := object.positiveDeficiency_le_boundaryIncidence
    (object.remainderSupport packing) threshold baseline
  rw [object.card_ordinaryDeficiencyReserve_remainderSupport threshold packing,
    object.card_windowRemainderIncidences packing]
  omega

/-- The reserve supply transported through the paper's exact window-join
identity.  This is a refinement bound on the new carrier family, not a second
capacity-token ledger. -/
theorem card_ordinaryDeficiencyReserve_windowJoinSupply
    (object : FiniteObject.{u}) {order threshold : Nat}
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking order packing)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (object.ordinaryDeficiencyReserve threshold packing
          (object.remainderSupport packing)).card +
        2 * (2 * (order - 1) * packing.card +
          (object.crossWindowIncidences packing).card) ≤
      2 * (threshold * (order * packing.card) +
        object.ambientSurplus (object.windowSupport packing) threshold) := by
  have reserve := object.card_ordinaryDeficiencyReserve_le_two_mul_windowBoundary
    threshold packing baseline
  have join := object.exact_window_join_identity valid baseline
  omega

end FiniteObject

namespace OrdinaryDeficiencyReserve

/-- Capacity of one ordinary-reserve carrier at the common candidate-ledger
scale `2s`: a positive-deficiency unit is a full unit, while a packed-window
incidence is a half unit. -/
def carrierCapacity (dischargeScale : Nat) (carrier : Carrier object) : Int :=
  match carrier with
  | .inl _ => 2 * (dischargeScale : Int)
  | .inr _ => dischargeScale

/-- Capacity of a literal finite ordinary-reserve family. -/
noncomputable def capacity (dischargeScale : Nat)
    (reserve : Finset (Carrier object)) : Int :=
  ∑ carrier ∈ reserve, carrierCapacity dischargeScale carrier

theorem capacity_nonnegative (dischargeScale : Nat)
    (reserve : Finset (Carrier object)) :
    0 ≤ capacity dischargeScale reserve := by
  classical
  apply Finset.sum_nonneg
  intro carrier _member
  rcases carrier with deficiency | incidence <;>
    simp [carrierCapacity]

theorem capacity_union {left right : Finset (Carrier object)}
    (disjoint : Disjoint left right) (dischargeScale : Nat) :
    capacity dischargeScale (left ∪ right) =
      capacity dischargeScale left + capacity dischargeScale right := by
  classical
  exact Finset.sum_union disjoint

theorem capacity_image_positiveDeficiency
    (units : Finset (PositiveDeficiencyUnit object))
    (dischargeScale : Nat) :
    capacity dischargeScale (units.image Sum.inl) =
      (2 * (dischargeScale : Int)) * units.card := by
  classical
  induction units using Finset.induction_on with
  | empty => simp [capacity]
  | @insert unit units absent ih =>
      simp [capacity, absent, ih, carrierCapacity]
      ring

theorem capacity_image_windowBoundary
    (units : Finset (WindowBoundaryUnit object))
    (dischargeScale : Nat) :
    capacity dischargeScale (units.image Sum.inr) =
      (dischargeScale : Int) * units.card := by
  classical
  induction units using Finset.induction_on with
  | empty => simp [capacity]
  | @insert unit units absent ih =>
      simp [capacity, absent, ih, carrierCapacity]
      ring

/-- Capacity is exactly additive over a pairwise-disjoint finite carrier
family. -/
theorem capacity_biUnion {Index : Type*} [DecidableEq Index]
    (dischargeScale : Nat) (indices : Finset Index)
    (family : Index → Finset (Carrier object))
    (disjoint : Set.PairwiseDisjoint (indices : Set Index) family) :
    capacity dischargeScale (indices.biUnion family) =
      ∑ index ∈ indices, capacity dischargeScale (family index) := by
  classical
  unfold capacity
  rw [Finset.sum_biUnion disjoint]

/-- The capacity of a support fibre is the exact sum of its singleton-anchor
fibres. -/
theorem capacity_anchorFibre_eq_sum_anchorFibreAt
    (dischargeScale : Nat) (reserve : Finset (Carrier object))
    (support : Finset object.Vertex) :
    capacity dischargeScale (anchorFibre reserve support) =
      ∑ vertex ∈ support,
        capacity dischargeScale (anchorFibreAt reserve vertex) := by
  classical
  rw [anchorFibre_eq_biUnion_anchorFibreAt]
  apply capacity_biUnion
  intro left _leftMember right _rightMember distinct
  exact anchorFibreAt_disjoint distinct

/-- Exact weighted additivity over any pairwise-disjoint finite family of
anchor supports. -/
theorem capacity_anchorFibre_biUnion {Index : Type*} [DecidableEq Index]
    (dischargeScale : Nat) (reserve : Finset (Carrier object))
    (indices : Finset Index) (supports : Index → Finset object.Vertex)
    (disjoint : Set.PairwiseDisjoint (indices : Set Index) supports) :
    capacity dischargeScale
        (anchorFibre reserve (indices.biUnion supports)) =
      ∑ index ∈ indices,
        capacity dischargeScale (anchorFibre reserve (supports index)) := by
  classical
  rw [anchorFibre_biUnion]
  apply capacity_biUnion
  intro left leftMember right rightMember distinct
  exact anchorFibre_disjoint (disjoint leftMember rightMember distinct)

end OrdinaryDeficiencyReserve

end

end Hypostructure.Graph

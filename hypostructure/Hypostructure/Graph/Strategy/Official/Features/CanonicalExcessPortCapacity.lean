/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT9 -> CT14).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Graph.Strategy.Official.Features.CanonicalDegreeThreePortResponse

/-!
# Capacity inherited from the canonical excess-port schedule

This file records the counting fact implicit in excess-port extraction:
distinct selected ports with a fixed centre inject into the graph-owned
neighbour suffix obtained after dropping the baseline threshold.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.CanonicalExcessPortCapacity

open Hypostructure.Graph
open CanonicalDegreeThreePortResponse

universe u v

variable
    {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}

abbrev Port :=
  ExcessPortExtraction.Port profile ctx.G

/-- A finite family whose rows retain literal membership in the canonical
excess-port schedule.  No application-selected classifier or capacity value
is part of this interface. -/
structure SelectedSubfamily where
  ports : List (Port (profile := profile) (ctx := ctx))
  nodup : ports.Nodup
  selected :
    ∀ port ∈ ports, port ∈ ExcessPortExtraction.ports profile ctx.G

noncomputable def SelectedSubfamily.centerMultiplicity
    (family : SelectedSubfamily (profile := profile) (ctx := ctx))
    (center : ctx.G.Vertex) : Nat := by
  classical
  exact (family.ports.filter fun port => decide (port.center = center)).length

private theorem port_eq_of_center_endpoint_eq
    (left right : Port (profile := profile) (ctx := ctx))
    (center : left.center = right.center)
    (endpoint : left.endpoint = right.endpoint) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem selected_endpoint_mem_suffix
    (family : SelectedSubfamily (profile := profile) (ctx := ctx))
    {port : Port (profile := profile) (ctx := ctx)}
    (member : port ∈ family.ports) :
    port.endpoint ∈
      (ctx.G.orderedNeighbors port.center).drop profile.threshold := by
  have selected := family.selected port member
  simp only [ExcessPortExtraction.ports, List.mem_flatMap,
    List.mem_map] at selected
  obtain ⟨center, centerMem, endpoint, endpointMem, equality⟩ := selected
  cases equality
  exact endpoint.2

/-- Any distinct selected subfamily has centre multiplicity bounded by the
literal degree slack at that centre. -/
theorem center_multiplicity_le_degree_sub_threshold
    (family : SelectedSubfamily (profile := profile) (ctx := ctx))
    (center : ctx.G.Vertex) :
    family.centerMultiplicity center ≤
      ctx.G.degree center - profile.threshold := by
  classical
  let rows := family.ports.filter fun port => decide (port.center = center)
  let endpoints := rows.map fun port => port.endpoint
  have rowsNodup : rows.Nodup := family.nodup.filter _
  have endpointsNodup : endpoints.Nodup := by
    apply rowsNodup.map_on
    intro left leftMem right rightMem endpointEq
    apply port_eq_of_center_endpoint_eq left right
    · have leftCenter :
          left.center = center := by
        exact of_decide_eq_true (List.mem_filter.mp leftMem).2
      have rightCenter :
          right.center = center := by
        exact of_decide_eq_true (List.mem_filter.mp rightMem).2
      exact leftCenter.trans rightCenter.symm
    · exact endpointEq
  have endpointSubset :
      endpoints.toFinset ⊆
        ((ctx.G.orderedNeighbors center).drop profile.threshold).toFinset := by
    intro endpoint endpointMem
    obtain ⟨port, portMem, endpointEq⟩ := List.mem_map.mp
      (List.mem_toFinset.mp endpointMem)
    have portFamilyMem : port ∈ family.ports :=
      (List.mem_filter.mp portMem).1
    have portCenter : port.center = center :=
      of_decide_eq_true (List.mem_filter.mp portMem).2
    apply List.mem_toFinset.mpr
    rw [← endpointEq, ← portCenter]
    exact selected_endpoint_mem_suffix family portFamilyMem
  calc
    family.centerMultiplicity center = rows.length := by
      rfl
    _ = endpoints.length := by simp [endpoints]
    _ = endpoints.toFinset.card := by
      exact (List.toFinset_card_of_nodup endpointsNodup).symm
    _ ≤ ((ctx.G.orderedNeighbors center).drop
          profile.threshold).toFinset.card :=
      Finset.card_le_card endpointSubset
    _ = ((ctx.G.orderedNeighbors center).drop
          profile.threshold).length := by
      exact List.toFinset_card_of_nodup
        (ctx.G.orderedNeighbors_nodup center).drop
    _ = ctx.G.degree center - profile.threshold := by
      rw [List.length_drop, ctx.G.orderedNeighbors_length]

end Hypostructure.Graph.Strategy.Official.Features.CanonicalExcessPortCapacity

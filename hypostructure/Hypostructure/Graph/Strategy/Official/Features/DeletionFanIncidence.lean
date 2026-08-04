import Hypostructure.Core.Strategy.Official.Features.DeletionFanAccounting
import Hypostructure.Graph.DeletionCriticality

/-!
# Deletion criticality to exact high-centre incidence data

The threshold is the threshold of the deletion-criticality profile.  Every
schedule below is computed from the active finite graph's declared order.
There is no authored centre list, port table, incidence table, or callback.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence

open Core.Strategy.Official.Features.DeletionFanAccounting

universe u v

variable
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {Target : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)}

/-- Canonical high centres, selected only from graph-derived degrees. -/
def highCenters (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) : List object.Vertex :=
  object.orderedVertices.filter fun vertex =>
    decide (profile.threshold < object.degree vertex)

@[simp] theorem mem_highCenters_iff
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) (vertex : object.Vertex) :
    vertex ∈ highCenters profile object ↔
      profile.threshold < object.degree vertex := by
  simp [highCenters]

theorem highCenters_nodup
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) :
    (highCenters profile object).Nodup :=
  object.orderedVertices_nodup.filter _

/-- One exact high-centre fan row.  Ports are the neighbours in the graph's
declared order; base and excess ports are projections, not authored data. -/
structure HighCenterRow
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) where
  center : object.Vertex
  high : profile.threshold < object.degree center

namespace HighCenterRow

def ports {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (row : HighCenterRow profile object) :
    List object.Vertex :=
  object.orderedNeighbors row.center

def base {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (row : HighCenterRow profile object) :
    List object.Vertex :=
  basePorts profile.threshold row.ports

def excess {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (row : HighCenterRow profile object) :
    List object.Vertex :=
  excessPorts profile.threshold row.ports

theorem ports_length {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (row : HighCenterRow profile object) :
    row.ports.length = object.degree row.center :=
  object.orderedNeighbors_length row.center

theorem base_length {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (row : HighCenterRow profile object) :
    row.base.length = profile.threshold := by
  apply Core.Strategy.Official.Features.DeletionFanAccounting.base_length
  rw [row.ports_length]
  exact Nat.le_of_lt row.high

theorem excess_length {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (row : HighCenterRow profile object) :
    row.excess.length = object.degree row.center - profile.threshold := by
  unfold excess
  rw [Core.Strategy.Official.Features.DeletionFanAccounting.excess_length
    profile.threshold row.ports]
  rw [row.ports_length]

theorem partition {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (row : HighCenterRow profile object) :
    row.base ++ row.excess = row.ports :=
  Core.Strategy.Official.Features.DeletionFanAccounting.base_append_excess _ _

end HighCenterRow

/-- Framework construction of every high-centre row. -/
def highCenterRows (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) :
    List (HighCenterRow profile object) :=
  (highCenters profile object).attach.map fun vertex =>
    ⟨vertex.1, (mem_highCenters_iff profile object vertex.1).mp vertex.2⟩

/-- Outside incidences at a port endpoint, retaining ambient order and
removing the centre itself. -/
def outsideIncidences (object : FiniteObject.{u})
    (center endpoint : object.Vertex) : List object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact (object.orderedNeighbors endpoint).erase center

theorem outsideIncidences_length
    (object : FiniteObject.{u}) {center endpoint : object.Vertex}
    (adjacent : object.graph.Adj center endpoint) :
    (outsideIncidences object center endpoint).length + 1 =
      object.degree endpoint := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [outsideIncidences, List.length_erase_add_one]
  · exact object.orderedNeighbors_length endpoint
  · exact (object.mem_orderedNeighbors_iff endpoint center).2 adjacent.symm

/-- One generated centre/port incidence. -/
structure PortIncidence
    (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) where
  center : object.Vertex
  centerHigh : profile.threshold < object.degree center
  endpoint : object.Vertex
  adjacent : object.graph.Adj center endpoint

namespace PortIncidence

def outside {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {object : FiniteObject.{u}} (incidence : PortIncidence profile object) :
    List object.Vertex :=
  outsideIncidences object incidence.center incidence.endpoint

end PortIncidence

/-- Canonical incidence rows generated from the canonical high-centre rows. -/
def incidenceRows (profile : DeletionCriticalityProfile Baseline)
    (object : FiniteObject.{u}) :
    List (PortIncidence profile object) :=
  (highCenterRows profile object).flatMap fun row =>
    row.ports.attach.map fun endpoint =>
      ⟨row.center, row.high, endpoint.1,
        (object.mem_orderedNeighbors_iff row.center endpoint.1).mp
          (by simpa [HighCenterRow.ports] using endpoint.2)⟩

/-- The complete exact residual handed from deletion criticality to later
fan strategies.  It retains the literal context and certificate. -/
structure Residual
    (profile : DeletionCriticalityProfile Baseline)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) Target
      (lexicographicProgress Baseline BranchState)) where
  criticality : DeletionCriticalityCertificate profile ctx
  centers : List (HighCenterRow profile ctx.G)
  centers_eq : centers = highCenterRows profile ctx.G
  incidences : List (PortIncidence profile ctx.G)
  incidences_eq : incidences = incidenceRows profile ctx.G

/-- Closed Graph constructor: all output data is computed from the graph and
the deletion certificate. -/
def deriveResidual
    (criticality : DeletionCriticalityCertificate profile ctx) :
    Residual profile ctx :=
  ⟨criticality, highCenterRows profile ctx.G, rfl,
    incidenceRows profile ctx.G, rfl⟩

namespace Residual

theorem centers_independent (residual : Residual profile ctx)
    {left right : ctx.G.Vertex}
    (left_mem : ∃ row ∈ residual.centers, row.center = left)
    (right_mem : ∃ row ∈ residual.centers, row.center = right) :
    ¬ ctx.G.graph.Adj left right := by
  rcases left_mem with ⟨leftRow, leftRowMem, rfl⟩
  rcases right_mem with ⟨rightRow, rightRowMem, rfl⟩
  apply residual.criticality.slackVerticesIndependent
  · exact leftRow.high
  · exact rightRow.high

theorem endpoint_tight (residual : Residual profile ctx)
    (row : HighCenterRow profile ctx.G) {endpoint : ctx.G.Vertex}
    (endpoint_mem : endpoint ∈ row.ports) :
    ctx.G.degree endpoint = profile.threshold := by
  have adjacent : ctx.G.graph.Adj row.center endpoint :=
    (ctx.G.mem_orderedNeighbors_iff row.center endpoint).mp endpoint_mem
  rcases residual.criticality.tightEndpoint
      ⟨(row.center, endpoint), adjacent⟩ with centerTight | endpointTight
  · exact False.elim ((Nat.ne_of_gt row.high) centerTight)
  · exact endpointTight

theorem outside_cardinality (residual : Residual profile ctx)
    (row : HighCenterRow profile ctx.G) {endpoint : ctx.G.Vertex}
    (endpoint_mem : endpoint ∈ row.ports) :
    (outsideIncidences ctx.G row.center endpoint).length + 1 =
      profile.threshold := by
  rw [outsideIncidences_length ctx.G
    ((ctx.G.mem_orderedNeighbors_iff row.center endpoint).mp endpoint_mem)]
  exact residual.endpoint_tight row endpoint_mem

theorem incidence_endpoint_tight (residual : Residual profile ctx)
    (incidence : PortIncidence profile ctx.G) :
    ctx.G.degree incidence.endpoint = profile.threshold := by
  rcases residual.criticality.tightEndpoint
      ⟨(incidence.center, incidence.endpoint), incidence.adjacent⟩ with
    centerTight | endpointTight
  · exact False.elim ((Nat.ne_of_gt incidence.centerHigh) centerTight)
  · exact endpointTight

theorem incidence_outside_cardinality (residual : Residual profile ctx)
    (incidence : PortIncidence profile ctx.G) :
    incidence.outside.length + 1 = profile.threshold := by
  rw [PortIncidence.outside,
    outsideIncidences_length ctx.G incidence.adjacent]
  exact residual.incidence_endpoint_tight incidence

/-- Work is derived solely from generated schedule lengths. -/
def work (residual : Residual profile ctx) :
    Core.Strategy.Official.Features.DeletionFanAccounting.Work
      ctx.G.orderedVertices.length
      (residual.centers.flatMap HighCenterRow.ports).length
      (residual.incidences.flatMap PortIncidence.outside).length :=
  Core.Strategy.Official.Features.DeletionFanAccounting.exactWork _ _ _

end Residual

end Hypostructure.Graph.Strategy.Official.Features.DeletionFanIncidence

import Hypostructure.Core.Strategy
import Hypostructure.Core.Strategy.LocalizedCompressionClosure
import Hypostructure.Graph.Object
import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.CT3
import Hypostructure.Graph.Strategy.ObstructionPackingClosure
import Hypostructure.Graph.Strategy.ScaleThresholdDichotomy
import Hypostructure.Graph.Strategy.AtomContextObstructionDichotomy
import Hypostructure.Graph.Strategy.FiniteStateCapacity
import Hypostructure.Graph.Strategy.ColdBranchPreludeAggregation
import Hypostructure.Graph.Strategy.CounterexampleLocalization
import Hypostructure.Graph.Strategy.TypeBFanClosure

/-!
# Graph adapters for reusable strategies

Graph supplies finite schedules and graph semantics.  Strategy ownership,
ledger composition, and terminal routing remain in Core.
-/

namespace Hypostructure.Graph.Strategy

universe u

open Hypostructure

/-- The canonical vertex scan for any finite graph strategy. -/
noncomputable def vertexScan (object : Graph.FiniteObject.{u}) :
    Core.Finite.Enumeration object.Vertex :=
  { values := object.orderedVertices
    nodup := object.orderedVertices_nodup
    decEq := object.vertices.decEq }

/-- The canonical schedule of a supplied induced support. -/
noncomputable def supportScan (object : Graph.FiniteObject.{u})
    (support : Finset object.Vertex) :
    Core.Finite.Enumeration {vertex : object.Vertex // vertex ∈ support} :=
  Graph.SupportComponents.Connected.schedule object support

/-- Generic graph witness-scan interface.  The graph-specific predicate is the
only application input; order and finite scheduling are framework-owned. -/
structure WitnessScan (Previous : Type u) where
  object : Core.Residual.Query Previous (fun _ => Graph.FiniteObject.{u})
  witness : (previous : Previous) -> (object.read previous).Vertex -> Prop
  witnessDecidable : (previous : Previous) ->
    (vertex : (object.read previous).Vertex) ->
      Decidable (witness previous vertex)

/-- Generic graph response interface for local finite coordinates. -/
structure ResponseProfile (Previous : Type u) where
  Coordinate : Previous -> Type u
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Coordinate previous))
  observe : (previous : Previous) -> Coordinate previous -> Bool

/-- Generic graph charge interface.  `charge` may be an integer graph charge,
while the Core capacity strategy can be instantiated with another quantity in
other domains. -/
structure ChargeProfile (Previous : Type u) where
  Item : Previous -> Type u
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  charge : (previous : Previous) -> Item previous -> Int

/-- Connected-support specialization used by the Type A/Type B split. -/
structure ConnectedSupportProfile (Previous : Type u) where
  object : Core.Residual.Query Previous (fun _ => Graph.FiniteObject.{u})
  support : Core.Residual.Query Previous (fun previous =>
    Finset (object.read previous).Vertex)

/-! ## Graph-to-Core strategy adapters

These constructors only package residual-owned graph profiles into the
domain-neutral Core contracts.  They do not execute a CT, choose a route, or
create a ledger value; those operations remain in Core's strategy runner. -/

noncomputable def WitnessScan.toCore
    (profile : WitnessScan Previous) :
    Core.Strategy.OrderedWitnessScan Previous where
  Item := fun previous => (profile.object.read previous).Vertex
  schedule := Core.Residual.Query.ofFunction fun previous =>
    vertexScan (profile.object.read previous)
  witness := profile.witness
  witnessDecidable := profile.witnessDecidable
  exhaustive := by
    intro previous vertex _membership
    letI := profile.witnessDecidable previous vertex
    by_cases h : profile.witness previous vertex
    · exact Or.inl h
    · exact Or.inr h

def ResponseProfile.toCore
    (profile : ResponseProfile Previous) :
    Core.Strategy.ResponseClassifier Previous where
  Item := profile.Coordinate
  Response := fun _ => Bool
  schedule := profile.schedule
  observe := profile.observe
  Class := fun _ => Bool
  classify := fun _ response => response
  exhaustive := by
    intro previous coordinate
    exact ⟨profile.observe previous coordinate, rfl⟩

def ChargeProfile.toCore
    (profile : ChargeProfile Previous)
    (classify : (previous : Previous) -> profile.Item previous -> Class)
    (capacity : (previous : Previous) -> Class -> Nat)
    (within : (previous : Previous) -> (item : profile.Item previous) ->
      Int.toNat (profile.charge previous item) ≤
        capacity previous (classify previous item)) :
    Core.Strategy.CapacityLedger Previous where
  Item := profile.Item
  Class := fun _ => Class
  schedule := profile.schedule
  classify := classify
  contribution := fun previous item => Int.toNat (profile.charge previous item)
  capacity := capacity
  totalWithin := within

noncomputable def ConnectedSupportProfile.toCore
    (profile : ConnectedSupportProfile Previous)
    (localBudget : (previous : Previous) ->
      {vertex : (profile.object.read previous).Vertex //
        vertex ∈ profile.support.read previous} -> Int)
    (selected : (previous : Previous) ->
      {vertex : (profile.object.read previous).Vertex //
        vertex ∈ profile.support.read previous})
    (selected_negative : (previous : Previous) ->
      localBudget previous (selected previous) < 0) :
    Core.Strategy.SupportLocalization Previous where
  Cell := fun previous =>
    {vertex : (profile.object.read previous).Vertex //
      vertex ∈ profile.support.read previous}
  schedule := Core.Residual.Query.ofFunction fun previous =>
    supportScan (profile.object.read previous) (profile.support.read previous)
  localBudget := localBudget
  selected := selected
  selected_negative := selected_negative

def targetAvoiding
    (target : Core.Residual.Query Previous (fun _ => Prop))
    (decidable : (previous : Previous) -> Decidable (target.read previous)) :
    Core.Strategy.TargetAvoidingContinuation Previous where
  Target := fun previous => target.read previous
  targetDecidable := decidable

def rankBudget
    (rank budget threshold : Previous -> Nat)
    (high low : Previous -> Prop)
    (exhaustive : (previous : Previous) -> high previous ∨ low previous) :
    Core.Strategy.RankBudgetSplit Previous where
  Rank := rank
  Budget := budget
  threshold := threshold
  high := high
  low := low
  exhaustive := exhaustive

def dichotomy
    {LeftPayload RightPayload : Previous -> Type u}
    (classify : (previous : Previous) ->
      Sum (LeftPayload previous) (RightPayload previous)) :
    Core.Strategy.Dichotomy Previous where
  LeftPayload := LeftPayload
  RightPayload := RightPayload
  classify := classify

noncomputable def connectedComponents
    (profile : ConnectedSupportProfile Previous) (previous : Previous) :
    List (Graph.SupportComponents.Connected.Component
      (profile.object.read previous) (profile.support.read previous)) :=
  Graph.SupportComponents.Connected.order
    (profile.object.read previous) (profile.support.read previous)

/-! ## Graph-to-Core registered data builders

These builders package residual-indexed graph inputs into the registered
`Core.*Data` families consumed only by the private strategy compiler.  They
interpret registered graph data at registration time, not execution time: no
builder receives or produces a stage, contract, route, or outcome.  Every
field is indexed by the initial residual `Core.Strategy.ProblemInput P`, so
the residual and ledger keep doing all data accounting. -/

/-- Registered vertex-scan family: one finite graph object per initial
residual, scheduled in the canonical vertex order, with an application-owned
decidable witness predicate.  Registration-time data for the
`orderedWitnessScan` key. -/
noncomputable def scanData (P : Core.Problem)
    (object : Core.Strategy.ProblemInput P -> Graph.FiniteObject.{u})
    (witness : (input : Core.Strategy.ProblemInput P) ->
      (object input).Vertex -> Prop)
    (witnessDecidable : (input : Core.Strategy.ProblemInput P) ->
      (vertex : (object input).Vertex) -> Decidable (witness input vertex)) :
    Core.ScanData P where
  Item := fun input => (object input).Vertex
  schedule := fun input => vertexScan (object input)
  witness := witness
  witnessDecidable := witnessDecidable

/-- Registered response-classification family over local finite coordinates
with Boolean observations classified by themselves, mirroring
`ResponseProfile.toCore`.  `ULift` carries `Bool` into the graph universe
because one registered family fixes a single data universe.
Registration-time data for the `responseClassifier` key. -/
def responseData (P : Core.Problem)
    (Coordinate : Core.Strategy.ProblemInput P -> Type u)
    (schedule : (input : Core.Strategy.ProblemInput P) ->
      Core.Finite.Enumeration (Coordinate input))
    (observe : (input : Core.Strategy.ProblemInput P) ->
      Coordinate input -> Bool) :
    Core.ResponseData P where
  Item := Coordinate
  Response := fun _ => ULift Bool
  Class := fun _ => ULift Bool
  schedule := schedule
  observe := fun input coordinate => ULift.up (observe input coordinate)
  classify := fun _ response => response

/-- Registered capacity account driven by an integer graph charge: the Core
contribution is the truncated nonnegative part of the charge, mirroring
`ChargeProfile.toCore`.  Registration-time data for the `capacityLedger`
key. -/
def capacityData (P : Core.Problem) {Class : Type u}
    (Item : Core.Strategy.ProblemInput P -> Type u)
    (schedule : (input : Core.Strategy.ProblemInput P) ->
      Core.Finite.Enumeration (Item input))
    (charge : (input : Core.Strategy.ProblemInput P) -> Item input -> Int)
    (classify : (input : Core.Strategy.ProblemInput P) -> Item input -> Class)
    (capacity : (input : Core.Strategy.ProblemInput P) -> Class -> Nat)
    (within : (input : Core.Strategy.ProblemInput P) ->
      (item : Item input) ->
        Int.toNat (charge input item) ≤
          capacity input (classify input item)) :
    Core.CapacityData P where
  Item := Item
  Class := fun _ => Class
  schedule := schedule
  classify := classify
  contribution := fun input item => Int.toNat (charge input item)
  capacity := capacity
  totalWithin := within

/-- Registered negative-budget localization over a supplied induced support:
cells are support members scheduled by the canonical connected-support order.
Registration-time data for the `supportLocalization` key. -/
noncomputable def localizationData (P : Core.Problem)
    (object : Core.Strategy.ProblemInput P -> Graph.FiniteObject.{u})
    (support : (input : Core.Strategy.ProblemInput P) ->
      Finset (object input).Vertex)
    (localBudget : (input : Core.Strategy.ProblemInput P) ->
      {vertex : (object input).Vertex // vertex ∈ support input} -> Int)
    (selected : (input : Core.Strategy.ProblemInput P) ->
      {vertex : (object input).Vertex // vertex ∈ support input})
    (selected_negative : (input : Core.Strategy.ProblemInput P) ->
      localBudget input (selected input) < 0) :
    Core.LocalizationData P where
  Cell := fun input =>
    {vertex : (object input).Vertex // vertex ∈ support input}
  schedule := fun input => supportScan (object input) (support input)
  localBudget := localBudget
  selected := selected
  selected_negative := selected_negative

/-- The connected components of a supplied induced support, scheduled by the
canonical connected-support order (`Graph.SupportComponents`) — the
"enlarge to a connected support" step of a rank-drop localization, expressed
as the region schedule `Core.Strategy.localizedCompressionClosure` needs. -/
noncomputable def componentSchedule (object : Graph.FiniteObject.{u})
    (support : Finset object.Vertex) :
    Core.Finite.Enumeration
      (Graph.SupportComponents.Connected.Component object support) where
  values := Graph.SupportComponents.Connected.order object support
  nodup := Core.Finite.ConnectedPartition.order_nodup _ _
  decEq := Classical.decEq _

/-- Registered localized-compression closure over a supplied induced
support: regions are its connected components (`componentSchedule`), and
each is checked for exact-response compression via a registered
`Graph.CT3.targetSpec`-shaped capability.  The one domain-specific
obligation — `bridge`, connecting a compression certificate to the
registered graph target — is optional and supplied by the caller: a real
search can be registered before its closing argument exists, without either
fabricating the search data or the closure (`Core.Strategy.
localizedCompressionClosure`'s `bridge := none` default).  Everything else
(the region schedule, the exhaustive per-region scan, and — when `bridge`
is supplied — the closure derivation) reuses `Core.Strategy.
localizedCompressionClosure` unchanged.  Registration-time data for a
`dichotomy` key. -/
noncomputable def componentCompressionData (P : Core.Problem)
    (T : Core.Target P)
    (object : Core.Strategy.ProblemInput P -> Graph.FiniteObject.{u})
    (support : (input : Core.Strategy.ProblemInput P) ->
      Finset (object input).Vertex)
    (spec : (input : Core.Strategy.ProblemInput P) ->
      Graph.SupportComponents.Connected.Component (object input) (support input) ->
      Hypostructure.CT3.Spec (Core.Strategy.ProblemInput P))
    (capability : (input : Core.Strategy.ProblemInput P) ->
      (c : Graph.SupportComponents.Connected.Component (object input)
        (support input)) -> Hypostructure.CT3.Capability (spec input c))
    (bridge : Option (PLift ((input : Core.Strategy.ProblemInput P) ->
      (c : Graph.SupportComponents.Connected.Component (object input)
        (support input)) ->
      Hypostructure.CT3.CompressionCertificate (capability input c) input ->
      T.Predicate input.object)) := none) :
    Core.DichotomyData P T :=
  Core.Strategy.localizedCompressionClosure
    (P := P) (T := T)
    (Component := fun input =>
      Graph.SupportComponents.Connected.Component (object input) (support input))
    (schedule := fun input => componentSchedule (object input) (support input))
    (spec := spec) (capability := capability) (bridge := bridge)

end Hypostructure.Graph.Strategy

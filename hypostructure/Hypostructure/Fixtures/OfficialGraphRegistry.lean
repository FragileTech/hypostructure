import Hypostructure.Graph.Strategy.Official.Registry

namespace Hypostructure.Fixtures.OfficialGraphRegistry

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official
open Hypostructure.Core.Strategy

abbrev object : FiniteObject where
  Vertex := Fin 3
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def data : Presentation where
  object := object
  acceptedReturnLengths := [2]

def v0 : data.object.Vertex := by change Fin 3; exact 0
def v1 : data.object.Vertex := by change Fin 3; exact 1
def v2 : data.object.Vertex := by change Fin 3; exact 2

example : v0 ∈ data.fanSchedule v1 := by
  letI : DecidableEq data.object.Vertex := data.object.vertices.decEq
  apply (data.mem_fanSchedule_iff v1 v0).2
  change (⊤ : SimpleGraph (Fin 3)).Adj 1 0
  simp
example : v2 ∈ data.fanSchedule v0 := by
  letI : DecidableEq data.object.Vertex := data.object.vertices.decEq
  apply (data.mem_fanSchedule_iff v0 v2).2
  change (⊤ : SimpleGraph (Fin 3)).Adj 0 2
  simp
example : (data.fanSchedule v1).length ≤ data.object.vertexCount :=
  data.fanSchedule_length_le_vertexCount v1

example :
    (Core.Strategy.OfficialRegistry.describe
      Core.Strategy.OfficialRegistry.Id.rootedReturn).owner =
        .graph := rfl

example :
    resolve data Core.Strategy.OfficialRegistry.Id.targetDecision = none := by
  simp [resolve]

example :
    resolve data
      Core.Strategy.OfficialRegistry.Id.representedFluxAccounting = none := by
  simp [resolve]

end Hypostructure.Fixtures.OfficialGraphRegistry

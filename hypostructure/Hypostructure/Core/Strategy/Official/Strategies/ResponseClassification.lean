import Hypostructure.Core.Strategy.Official.Strategies.Common

namespace Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification

def Fibre (slot : FunctionTableSlot) (y : slot.right.Carrier) :=
  slot.rows.filter fun row => decide (row.2 = y)

/-- Exact terminal retaining the complete response graph and every canonical
response fibre.  Classification is equality in the slot's response carrier. -/
structure Terminal (slot : FunctionTableSlot) where
  graph : List (slot.left.Carrier × slot.right.Carrier)
  graph_eq : graph = slot.rows
  domainCovered : ∀ x, x ∈ graph.map Prod.fst
  functional : ∀ {x y z}, (x, y) ∈ graph → (x, z) ∈ graph → y = z
  fibres : slot.right.Carrier → List (slot.left.Carrier × slot.right.Carrier)
  fibres_eq : fibres = Fibre slot
  work : Strategies.StaticWork graph.length

def execute (slot : FunctionTableSlot) : Terminal slot :=
  { graph := slot.rows
    graph_eq := rfl
    domainCovered := fun x => Strategies.mem_map_fst (slot.total x)
    functional := slot.functional
    fibres := Fibre slot
    fibres_eq := rfl
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification

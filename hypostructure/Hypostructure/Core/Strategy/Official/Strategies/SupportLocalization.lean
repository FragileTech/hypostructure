import Hypostructure.Core.Strategy.Official.Strategies.Common

namespace Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization

def Support (slot : RelationSlot) : List slot.left.Carrier :=
  slot.rows.map Prod.fst

def Fibre (slot : RelationSlot) (x : slot.left.Carrier) :
    List (slot.left.Carrier × slot.right.Carrier) :=
  slot.rows.filter fun row => decide (row.1 = x)

/-- Literal support and all local fibres derived by Core from one relation. -/
structure Terminal (slot : RelationSlot) where
  relation : List (slot.left.Carrier × slot.right.Carrier)
  relation_eq : relation = slot.rows
  support : List slot.left.Carrier
  support_eq : support = relation.map Prod.fst
  fibres : slot.left.Carrier → List (slot.left.Carrier × slot.right.Carrier)
  fibres_eq : fibres = Fibre slot
  work : Strategies.StaticWork relation.length

def execute (slot : RelationSlot) : Terminal slot :=
  { relation := slot.rows
    relation_eq := rfl
    support := Support slot
    support_eq := rfl
    fibres := Fibre slot
    fibres_eq := rfl
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization

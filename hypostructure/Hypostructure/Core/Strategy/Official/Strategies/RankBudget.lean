import Hypostructure.Core.Strategy.Official.Strategies.Common

namespace Hypostructure.Core.Strategy.Official.Strategies.RankBudget

def maximum (slot : NatTableSlot) : Nat :=
  (slot.rows.map Prod.snd).foldl Nat.max 0

/-- Exact rank spectrum and framework-computed maximum.  Threshold comparison
is deliberately left to a later official strategy supplied with a bound slot. -/
structure Terminal (slot : NatTableSlot) where
  spectrum : List (slot.key.Carrier × Nat)
  spectrum_eq : spectrum = slot.rows
  coordinateCovered : ∀ x, x ∈ spectrum.map Prod.fst
  uniqueRank : ∀ {x m n}, (x, m) ∈ spectrum → (x, n) ∈ spectrum → m = n
  maxRank : Nat
  maxRank_eq : maxRank = (spectrum.map Prod.snd).foldl Nat.max 0
  work : Strategies.StaticWork spectrum.length

def execute (slot : NatTableSlot) : Terminal slot :=
  { spectrum := slot.rows
    spectrum_eq := rfl
    coordinateCovered := fun x => Strategies.mem_map_fst (slot.total x)
    uniqueRank := slot.functional
    maxRank := maximum slot
    maxRank_eq := rfl
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.RankBudget

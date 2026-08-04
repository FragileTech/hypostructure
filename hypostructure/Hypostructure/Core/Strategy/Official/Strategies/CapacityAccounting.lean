import Hypostructure.Core.Strategy.Official.Strategies.Common

namespace Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

def totalMass (slot : NatTableSlot) : Nat :=
  (slot.rows.map Prod.snd).sum

/-- Exact deterministic ledger and its framework-computed aggregate. -/
structure Terminal (slot : NatTableSlot) where
  ledger : List (slot.key.Carrier × Nat)
  ledger_eq : ledger = slot.rows
  payerCovered : ∀ x, x ∈ ledger.map Prod.fst
  uniqueCharge : ∀ {x m n}, (x, m) ∈ ledger → (x, n) ∈ ledger → m = n
  aggregate : Nat
  aggregate_eq : aggregate = (ledger.map Prod.snd).sum
  work : Strategies.StaticWork ledger.length

def execute (slot : NatTableSlot) : Terminal slot :=
  { ledger := slot.rows
    ledger_eq := rfl
    payerCovered := fun x => Strategies.mem_map_fst (slot.total x)
    uniqueCharge := slot.functional
    aggregate := totalMass slot
    aggregate_eq := rfl
    work := Strategies.exactWork slot.rows.length }

end Hypostructure.Core.Strategy.Official.Strategies.CapacityAccounting

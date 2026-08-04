import Hypostructure.Core.Strategy.Official.Features.DeletionFanAccounting

namespace Hypostructure.Fixtures.S09S10Accounting

open Core.Strategy.Official.Features.DeletionFanAccounting

def rows : List (LoadRow Nat) :=
  [⟨0, 2⟩, ⟨1, 4⟩, ⟨2, 3⟩, ⟨3, 5⟩]

example : (highRows 3 rows).map LoadRow.item = [1, 3] := by decide
example : basePorts 3 [10, 11, 12, 13, 14] = [10, 11, 12] := by decide
example : excessPorts 3 [10, 11, 12, 13, 14] = [13, 14] := by decide
example : (exactWork 4 7 9).bound = 20 := by decide

def ledger : ThresholdLedger Nat :=
  deriveThresholdLedger 3 rows

example (row : LoadRow Nat) (member : row ∈ ledger.source) :
    row ∈ ledger.high ∨ row ∈ ledger.ordinary :=
  ledger.source_classified row member

example : List.Disjoint ledger.high ledger.ordinary :=
  ledger.high_disjoint_ordinary

#print axioms Core.Strategy.Official.Features.DeletionFanAccounting.base_append_excess
#print axioms Core.Strategy.Official.Features.DeletionFanAccounting.excess_length
#print axioms Core.Strategy.Official.Features.DeletionFanAccounting.ThresholdLedger.source_classified

end Hypostructure.Fixtures.S09S10Accounting

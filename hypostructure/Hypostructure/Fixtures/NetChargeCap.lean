import Hypostructure.Graph.NetCharge

/-!
# Exact finite net-cap fixture

The node-`[60]` arithmetic is a generic graph statement: exact stub supply plus
the cleared strict quarter-cap forces negative net charge.  This fixture keeps
the implication independent of the EG vocabulary and checks that no
enumeration, native reduction, or proof-specific carrier is needed.
-/

namespace Hypostructure.Fixtures.NetChargeCap

open Hypostructure.Graph

universe u

example (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold dischargeScale debit capacity : Nat)
    (stubSupply :
      object.positiveDeficiency support threshold + debit ≤ capacity)
    (strictCap :
      dischargeScale * capacity < dischargeScale * debit + support.card) :
    object.NegativeNetCharge support threshold dischargeScale :=
  object.negativeNetCharge_of_stubSupply_of_strictCap support threshold
    dischargeScale debit capacity stubSupply strictCap

end Hypostructure.Fixtures.NetChargeCap

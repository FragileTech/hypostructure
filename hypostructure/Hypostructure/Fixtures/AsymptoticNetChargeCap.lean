import Hypostructure.Graph.NetCharge

namespace Hypostructure.Fixtures.AsymptoticNetChargeCap

open Graph

example (object : Graph.FiniteObject) (support : Finset object.Vertex)
    (threshold dischargeScale windowOrder windowRate surplusScale size packingCard : Nat)
    (windowOrderPos : 0 < windowOrder) (thresholdPos : 0 < threshold)
    (debitLe : 2 * (windowOrder - 1) ≤ threshold * windowOrder)
    (rateSlack : Graph.FiniteObject.netCapWindowCost threshold dischargeScale windowOrder * threshold <
      2 * windowRate)
    (large : Graph.FiniteObject.SufficientlyLargeForNetCap threshold dischargeScale
      windowOrder windowRate surplusScale size)
    (densityCap : 2 * (windowRate * Nat.log2 size * packingCard) ≤
      (Nat.log2 size + 1) * (threshold * size + surplusScale * Core.ceilSqrt size))
    (supportCardIdentity : windowOrder * packingCard + support.card = size)
    (stubSupply : object.positiveDeficiency support threshold + 2 * (windowOrder - 1) * packingCard ≤
      threshold * (windowOrder * packingCard) + surplusScale * Core.ceilSqrt size) :
    object.NegativeNetCharge support threshold dischargeScale :=
  object.negativeNetCharge_of_stubSupply_of_densityCap_of_sufficientlyLarge support
    threshold dischargeScale windowOrder windowRate surplusScale size packingCard
    windowOrderPos thresholdPos debitLe rateSlack large densityCap supportCardIdentity stubSupply

example (threshold dischargeScale windowOrder windowRate surplusScale size : Nat)
    (large : Graph.FiniteObject.netCapCutoff threshold dischargeScale windowOrder windowRate surplusScale ≤ size) :
    Graph.FiniteObject.SufficientlyLargeForNetCap threshold dischargeScale windowOrder
      windowRate surplusScale size :=
  Graph.FiniteObject.sufficientlyLargeForNetCap_of_cutoff threshold dischargeScale
    windowOrder windowRate surplusScale size large

end Hypostructure.Fixtures.AsymptoticNetChargeCap

import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Strategy.LocalSupplyLowerBoundSemantics

namespace Hypostructure.Core.Strategy.FiniteStateNetChargeContinuation

open Hypostructure.Core.Residual

universe uStage uNew

/-- Query-only view of the exact selected finite-state-capacity ledger entry.
It owns no values and performs no write.

Every entry is branch-independent: the seven values are read off the literal
predecessor, and `scaledDeficiency` is the local-supply accounting's own finite
cap.  Nothing here records which alternative of the entropy split was taken,
so both alternatives of `prop:two-budget` publish the same ledger. -/
structure CapacityLedger (Stage : Type uStage) where
  localSupply : Query Stage (fun _ => LocalSupplyLowerBound.Summary)
  forcedPower : Query Stage (fun _ => Nat)
  flatPower : Query Stage (fun _ => Nat)
  realizedStateCount : Query Stage (fun _ => Nat)
  ambientOrder : Query Stage (fun _ => Nat)
  remainderCard : Query Stage (fun _ => Nat)
  statePowerExponent : Query Stage (fun _ => Nat)
  scaledDeficiency : Query Stage fun stage =>
    (localSupply.read stage).netDeficiency.scale *
        (localSupply.read stage).netDeficiency.deficiency ≤
      (localSupply.read stage).netDeficiency.coefficient *
          (localSupply.read stage).netDeficiency.remainder +
        (localSupply.read stage).netDeficiency.scale *
          (localSupply.read stage).netDeficiency.surplus

namespace CapacityLedger

/-- Transport the same query handles through a framework-owned projection. -/
def comap (ledger : CapacityLedger Stage) (project : NewStage → Stage) :
    CapacityLedger NewStage where
  localSupply := ledger.localSupply.comap project
  forcedPower := ledger.forcedPower.comap project
  flatPower := ledger.flatPower.comap project
  realizedStateCount := ledger.realizedStateCount.comap project
  ambientOrder := ledger.ambientOrder.comap project
  remainderCard := ledger.remainderCard.comap project
  statePowerExponent := ledger.statePowerExponent.comap project
  scaledDeficiency := ledger.scaledDeficiency.comap project

def preserve {Added : Stage → Type uNew}
    (ledger : CapacityLedger Stage) :
    CapacityLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

def preserveProp {Added : Stage → Prop}
    (ledger : CapacityLedger Stage) :
    CapacityLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

end CapacityLedger

/-- Empty registration selecting the built-in ledger continuation.  It has no
classifier, route, terminal, result, or target-closure field: Core computes
the zero/positive split and always publishes both sides as residuals. -/
structure Registration (_Residual : Type uStage) (_Target : _Residual → Prop) where

end Hypostructure.Core.Strategy.FiniteStateNetChargeContinuation

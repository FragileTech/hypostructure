import Hypostructure.CT13.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT13

This adapter evaluates primitive tiered-resource semantics against a finite
graph object read from the incoming ledger.  It creates no candidate family,
fallback, reconciliation ledger, outcome, or route.
-/

namespace Hypostructure.Graph.CT13

universe uPrevious uPayer uObstruction uResource uVertex

/-- Translate graph-indexed primitive semantics into the shared CT13 spec. -/
def tieredSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Payer : Previous -> Type uPayer)
    (Obstruction : Previous -> Type uObstruction)
    (Resource : Previous -> Type uResource)
    (eligible : (previous : Previous) -> FiniteObject.{uVertex} ->
      Payer previous -> Prop)
    (obstructionCost : (previous : Previous) -> FiniteObject.{uVertex} ->
      Obstruction previous -> Nat)
    (payerResource : (previous : Previous) -> FiniteObject.{uVertex} ->
      Payer previous -> Resource previous)
    (charge : (previous : Previous) -> FiniteObject.{uVertex} ->
      Payer previous -> Nat)
    (demand : (previous : Previous) -> FiniteObject.{uVertex} -> Nat) :
    _root_.Hypostructure.CT13.Spec Previous where
  Payer := Payer
  Obstruction := Obstruction
  Resource := Resource
  Eligible := fun previous payer =>
    eligible previous (object previous) payer
  obstructionCost := fun previous obstruction =>
    obstructionCost previous (object previous) obstruction
  payerResource := fun previous payer =>
    payerResource previous (object previous) payer
  charge := fun previous payer =>
    charge previous (object previous) payer
  demand := fun previous => demand previous (object previous)

/-- Supply only inherited schedules, primitive graph decisions, and a work
envelope to the common CT13 executor. -/
def tieredCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Payer : Previous -> Type uPayer)
    (Obstruction : Previous -> Type uObstruction)
    (Resource : Previous -> Type uResource)
    (eligible : (previous : Previous) -> FiniteObject.{uVertex} ->
      Payer previous -> Prop)
    (obstructionCost : (previous : Previous) -> FiniteObject.{uVertex} ->
      Obstruction previous -> Nat)
    (payerResource : (previous : Previous) -> FiniteObject.{uVertex} ->
      Payer previous -> Resource previous)
    (charge : (previous : Previous) -> FiniteObject.{uVertex} ->
      Payer previous -> Nat)
    (demand : (previous : Previous) -> FiniteObject.{uVertex} -> Nat)
    (payers : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Payer previous))
    (obstructions : Core.Residual.Query Previous fun previous =>
      _root_.Hypostructure.CT13.ObstructionSchedule
        (Obstruction previous))
    (tierTwo : Core.Residual.Query Previous fun previous =>
      (obstruction : Obstruction previous) ->
        Core.Finite.Enumeration (Payer previous))
    (eligibleDecidable : (previous : Previous) ->
      (graph : FiniteObject.{uVertex}) -> (payer : Payer previous) ->
        Decidable (eligible previous graph payer))
    (resourceDecidableEq : (previous : Previous) ->
      DecidableEq (Resource previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT13.localCheckBound
        (payers previous) (obstructions previous)
        (tierTwo previous) <=
          workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT13.Capability
      (tieredSpec object Payer Obstruction Resource eligible obstructionCost
        payerResource charge demand) where
  payers := payers
  obstructions := obstructions
  tierTwo := tierTwo
  eligibleDecidable := fun previous payer =>
    eligibleDecidable previous (object previous) payer
  resourceDecidableEq := resourceDecidableEq
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT13

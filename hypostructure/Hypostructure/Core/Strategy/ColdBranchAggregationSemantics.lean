import Hypostructure.Core.Finite.ColdCorridor
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Strategy.ProblemInput
import Hypostructure.Core.Strategy.ObstructionPackingData
import Hypostructure.Core.Strategy.ObstructionPackingSemantics
import Hypostructure.Core.Strategy.InterfaceReplacement

namespace Hypostructure.Core.Strategy.ColdBranchAggregation

open Hypostructure.Core.Residual

universe uStage uNew uResidual uPacking uHandoff uOwner uItem uState uOutput
  uAmbient uBranch uMeasure uInterface uSite uAtom uContext uSignature

/-- Query-only view of the exact finite-density overflow ledger entry. -/
structure OverflowLedger (Stage : Type uStage) where
  lowerMass : Query Stage (fun _ => Nat)
  capacity : Query Stage (fun _ => Nat)
  overflow : Query Stage fun stage =>
    capacity stage < lowerMass stage

namespace OverflowLedger

def comap (ledger : OverflowLedger Stage) (project : NewStage → Stage) :
    OverflowLedger NewStage where
  lowerMass := ledger.lowerMass.comap project
  capacity := ledger.capacity.comap project
  overflow := ledger.overflow.comap project

def preserve {Added : Stage → Type uNew} (ledger : OverflowLedger Stage) :
    OverflowLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

def preserveProp {Added : Stage → Prop} (ledger : OverflowLedger Stage) :
    OverflowLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

end OverflowLedger

/-- Exact cold-family capability at one literal ledger stage.  Both the owner
carrier and the producer query stay indexed by that stage, so later execution
cannot reconstruct either value from the stable residual alone.

`classifiedStateForcesTarget` follows
`ObstructionPackingClosure.Semantics.freeForcesTarget` at
`Core/Strategy/ObstructionPackingSemantics.lean:29`: inert presentation data
owned by the registering layer.  It consumes the *single* classified cold
ledger record, so Core performs no partition analysis of its own. -/
structure FamilyCapability (Previous : Type uStage) (Target : Previous → Prop) where
  Owner : Previous → Type uOwner
  family : Query Previous fun previous =>
    Core.Finite.ColdCorridor.Producer.FamilyProducer.{
      uOwner, uItem, uState, uOutput} (Owner previous)
  storedF1ForcesTarget : (previous : Previous) →
    (stage : (family previous).ClassifiedStateStage Previous) →
    (family previous).FailureOwner
        ((family previous).storedClassificationQuery stage) .f1 →
      Target previous
  classifiedStateForcesTarget : (previous : Previous) →
    (stage : (family previous).ClassifiedStateStage Previous) →
      Option (PLift (Target previous))

/-- Stage-polymorphic registration of the exact family capability consumed by
the cold continuation.  Core supplies both the live packing and the upstream
handoff-support queries; the registration may only return a query on that same
stage.  In particular, this boundary has no
`Residual → Packing → FamilyProducer` callback and no support schedule. -/
structure LedgerRegistration
    (P : Core.Problem.{uAmbient, uBranch}) (T : Core.Target P)
    (progress : Core.Progress.{uAmbient, uBranch, uMeasure} P)
    (replacement : Core.Strategy.InterfaceReplacement.Profile.{
      uAmbient, uBranch, uMeasure, uInterface, uSite, uAtom, uContext,
      uSignature} (P := P) (T := T) progress)
    (packingSemantics :
      ObstructionPackingClosure.Semantics.{max uAmbient uBranch, uPacking}
        (Core.Strategy.ProblemInput P)
        (fun input => T.Predicate input.object))
    (HandoffSupport : Core.Strategy.ProblemInput P → Type uHandoff) where
  atStage :
    {Previous : Type uStage} →
    [HasResidual Previous (Core.Strategy.ProblemInput P)] →
    (exact : Core.Strategy.InterfaceReplacement.ExactClosureQueries
      replacement Previous) →
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P) →
    /- The provenance law of the retained minimal-closure header, read at this
    stage: the object the spine is arguing about is the object that header
    publishes.  It is read by the canonical
    `ExactLedger.minimalClosureActiveObject` accessor, already proved for this reduction
    index, and it is what makes `exact.closure` speak about the active
    object rather than about an unrelated one. -/
    (activeObject : Query Previous fun previous =>
      (current previous).object = (exact.context previous).G) →
    (packing : Query Previous fun previous =>
      ObstructionPackingClosure.Packing
        (packingSemantics.occurrences (current previous))
        (packingSemantics.conflict (current previous))) →
    (handoffSupports : Query Previous (fun previous =>
      Core.Finite.Enumeration
        (HandoffSupport (current previous)))) →
    (handoffAbsent : Option (PLift (∀ previous,
      (handoffSupports previous).values = []))) →
    FamilyCapability.{uStage, uOwner, uItem, uState, uOutput} Previous
      (fun previous => T.Predicate (current previous).object)

end Hypostructure.Core.Strategy.ColdBranchAggregation

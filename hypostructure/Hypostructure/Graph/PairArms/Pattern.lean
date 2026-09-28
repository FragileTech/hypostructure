import Hypostructure.Graph.PairArms.Separated

/-!
# Pair code, arm A: role fibres and the live roles

Vocabulary-free.  A pair in a role fibre of an object capacity ledger is scheduled, charged
to the fibre's token, and carries the fibre's role (`mem_roleFibre_charge`); `liveRoles`
lists the ten `(blocker kind, token subtype)` roles a charged pair can carry at a recorded
activation.
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure Hypostructure.Graph Hypostructure.Graph.FiniteObject
open Hypostructure.Graph.SameTokenBlockerRoles

universe u

/-- Membership in a role fibre of an object capacity ledger, read at the charge. -/
theorem mem_roleFibre_charge {object : Graph.FiniteObject.{u}} {threshold order : Nat}
    {cap : CapacityPresentation object threshold order}
    (ledger : ObjectCapacityLedger object threshold order cap)
    {token : CapacityToken object} {role : SameTokenBlockerRoles.Role}
    {pair : Finset ledger.presented.Demand}
    (h : pair ∈ ledger.presented.roleFibre token role) :
    pair ∈ object.portPairSchedule threshold ∧
      capacityCharge cap.activation cap.carrier threshold cap.packing pair = some token ∧
      capacityRole cap.activation cap.carrier threshold cap.packing pair = role := by
  classical
  unfold CapacityTokenLedger.roleFibre PatternFamily.roleFibre CapacityTokenLedger.fibre at h
  rw [Finset.mem_filter, Finset.mem_filter] at h
  obtain ⟨⟨hs, hl⟩, hr⟩ := h
  refine ⟨hs, ?_, hr⟩
  have hl' : CanonicalFibreLedger.canonicalLabel (capacityTokenOrder object threshold cap.packing)
      (Charges cap.activation cap.carrier threshold cap.packing) pair = some token := hl
  rwa [canonicalLabel_eq_capacityCharge] at hl'

/-- The ten roles that can carry a charged pair at a recorded activation. -/
def liveRoles : List (BlockerKind × TokenSubtype) :=
  [(.sharedDeclaredSupport, .primitiveVertex), (.sharedDeclaredSupport, .remainderSurplus),
   (.sharedReturnSupport, .primitiveVertex), (.sharedReturnSupport, .remainderSurplus),
   (.targetResponse, .boundaryWindow), (.targetResponse, .crossWindow),
   (.targetResponse, .remainderSurplus), (.targetResponse, .primitiveVertex),
   (.arithmeticChordSet, .primitivePort), (.arithmeticChordSet, .remainderSurplus)]

end Hypostructure.Graph.PairArms

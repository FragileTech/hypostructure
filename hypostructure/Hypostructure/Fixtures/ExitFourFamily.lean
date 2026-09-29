import Hypostructure.Graph.ExitFourFamily

/-! Compile-time checks for the closed manuscript Q1--Q5 family. -/

namespace Hypostructure.Fixtures.ExitFourFamily

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.ExitFour

universe u

variable {Target : FiniteObject.{u} → Prop} {object : FiniteObject.{u}}
variable {support : Finset object.Vertex} {threshold scale : Nat}
variable {receiver load : object.Vertex}

example (datum : Q1TargetDefect Target support threshold scale receiver load) :
    (CanonicalMember.q1 datum).clause = ReceiverClause.visibleEntry := rfl

-- A Q1 datum must compare the two response pieces of its own selected pair,
-- read in G's own surroundings `G − X`.  An arbitrary target-defective graph
-- replacement cannot occupy this field.
example (datum : Q1TargetDefect Target support threshold scale receiver load) :
    ¬ (Target (glue (visibleResponsePiece datum.pair.leftResponseCoordinate)
        (Strategy.InterfaceReplacement.SupportAtom.outside object support)) ↔
      Target (glue (visibleResponsePiece datum.pair.rightResponseCoordinate)
        (Strategy.InterfaceReplacement.SupportAtom.outside object support))) :=
  datum.targetDefect

-- Stated about G, a Q1 datum cannot occur at a target-avoiding G.
example {L : Nat → Prop} (avoids : ¬ HasCycleWithLength L object)
    (datum : Q1TargetDefect (HasCycleWithLength L) support threshold scale
      receiver load) : False :=
  datum.false_of_avoids avoids

example (datum : Q5TargetDefect Target support threshold scale receiver load) :
    (CanonicalMember.q5 datum).clause = ReceiverClause.carrierDeletion := rfl

example {peeled : Finset object.Vertex}
    (witness : Witness Target support threshold scale receiver peeled) :
    witness.load ∈ object.routedLoads support threshold receiver :=
  witness.routed

end Hypostructure.Fixtures.ExitFourFamily

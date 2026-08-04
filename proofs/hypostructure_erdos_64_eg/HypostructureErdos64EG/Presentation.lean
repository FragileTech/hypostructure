import Hypostructure.Graph.TypeABCertificate
import Hypostructure.Graph.External.HegdeSandeepShashank
import HypostructureErdos64EG.Problem

/-!
# The shared Type-A / Type-B presentation

`Graph.TypeAB.Presentation` is the record the Type-A and Type-B propositions
read.  Both the official registry and the A/B registry need it -- the official
one for the Type A receiver-exhaustion registrations of manuscript nodes
`[86]`--`[109]`, the A/B one for the global Type-A and Type-B propositions -- so
it is declared once here, above both.

Every field is a projection of an already registered datum, and no numeral
appears: the manuscript's `3` is the registered baseline degree, its `P₁₃` is the
registered induced-path order, and its `α = 1/4` is the reciprocal of the
registered profile's own `loadMultiplier`.
-/

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-- The registered baseline degree.  The manuscript's `3` is this value. -/
abbrev baselineDegree : Nat := erdosReceiverLoadProfile.baselineDegree

/-- The registered induced-path order.  The manuscript's `P₁₃` is this value. -/
abbrev inducedPathOrder : Nat :=
  Graph.External.HegdeSandeepShashank.inducedPathOrder

/-- The registered discharge scale `1/α`.  The manuscript's `α = 1/4` of
`lem:typeA-unsaturated-discharge` is the reciprocal of this value, which is the
registered profile's own `loadMultiplier`. -/
abbrev dischargeScale : Nat := erdosReceiverLoadProfile.loadMultiplier

/-- The carrier parity of `lem:typeA-carrier-cut-parity`: a surviving mixed
target event crosses the support cut an even, positive number of times, so it
records at least this many distinct essential carriers.  It is the arity of a
cut crossing -- an edge has two ends -- and not a tuned constant. -/
abbrev carrierParity : Nat := 2

/-- `prop:typeA-route8-carrier-reduction`'s private-carrier demand: one more
than the cut parity, the manuscript's "at least three private essential
carriers" at node `[119]`.

Both this and `dischargeScale` are what make node `[122]`'s `3/13` derived
rather than written: the rate premise there is `RateCap56` at
`num := requiredPrivateCount` and `den := requiredPrivateCount · dischargeScale
+ 1`, which at the registered values is `3 / (3 · 4 + 1)`. -/
abbrev requiredPrivateCount : Nat := carrierParity + 1

/-- The presentation the Type-A/Type-B declarations read.  Every field is a
projection of an already registered datum. -/
def presentation : Graph.TypeAB.Presentation.{u} where
  baselineDegree := baselineDegree
  inducedPathOrder := inducedPathOrder
  dischargeScale := dischargeScale
  Target := HypostructureErdos64EG.Target
  LengthOK := PowerOfTwoLength

end HypostructureErdos64EG

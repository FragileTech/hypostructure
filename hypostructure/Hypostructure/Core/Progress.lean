import Hypostructure.Core.Problem

/-!
# Optional structural progress

A progress profile is an explicit capability. Core clients that do not perform
minimality or well-founded recursion do not need one.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uMeasure

/-- A well-founded measure available to tactics that require strict progress. -/
structure Progress (P : Problem.{uAmbient, uBranch}) where
  Measure : Type uMeasure
  lt : Measure -> Measure -> Prop
  wellFounded : WellFounded lt
  measure : P.Ambient -> Measure

namespace Progress

variable {P : Problem.{uAmbient, uBranch}}

/-- The strict ambient-object relation induced by a progress profile. -/
def Smaller (progress : Progress.{uAmbient, uBranch, uMeasure} P)
    (G H : P.Ambient) : Prop :=
  progress.lt (progress.measure G) (progress.measure H)

/-- Pulling back a well-founded measure relation remains well-founded. -/
theorem wellFounded_smaller
    (progress : Progress.{uAmbient, uBranch, uMeasure} P) :
    WellFounded progress.Smaller := by
  change WellFounded
    (fun G H => progress.lt (progress.measure G) (progress.measure H))
  exact progress.wellFounded.onFun

/-- No ambient object is strictly smaller than itself. -/
theorem not_smaller_self
    (progress : Progress.{uAmbient, uBranch, uMeasure} P) (G : P.Ambient) :
    Not (progress.Smaller G G) :=
  progress.wellFounded_smaller.irrefl.irrefl G

/-- Equal measures cannot certify a strict replacement. -/
theorem not_smaller_of_measure_eq
    (progress : Progress.{uAmbient, uBranch, uMeasure} P)
    {G H : P.Ambient} (measure_eq : progress.measure G = progress.measure H) :
    Not (progress.Smaller G H) := by
  intro smaller
  apply progress.wellFounded.irrefl.irrefl (progress.measure H)
  simpa [Smaller, measure_eq] using smaller

/-- Transport a progress profile across any two problems sharing the same
`Ambient` type. `Progress` depends on nothing else about its problem (not
`Baseline`, not `BranchState`, and not `Presentation`/`presentation`), so
this transport is total, free, and needs no new mathematics: a profile
registered once for a bare `Graph.problem`/`PDE.problem` is automatically
reusable for any presentation-bearing extension of the same problem (e.g.
`Graph.problemWithPresentation`) with the same `Ambient`, without every
such extension re-registering its own copy. -/
def ofAmbientEq {P Q : Problem.{uAmbient, uBranch}}
    (h : Q.Ambient = P.Ambient) (progress : Progress.{uAmbient, uBranch, uMeasure} P) :
    Progress.{uAmbient, uBranch, uMeasure} Q where
  Measure := progress.Measure
  lt := progress.lt
  wellFounded := progress.wellFounded
  measure := fun G => progress.measure (h ▸ G)

end Progress

end Hypostructure.Core

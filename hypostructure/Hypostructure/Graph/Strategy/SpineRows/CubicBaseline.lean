import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[67]`, the standing law: the high-neighbourhood normal form

`lem:heavy-neighbourhood-normal-form`.  At a high centre `h` -- one whose degree
is strictly above the baseline -- the manuscript proves three things, and the
whole Type B fan analysis runs on them:

* (a) every vertex of `N_G(h)` has degree exactly the baseline;
* (b) `G[N_G(h)]` is a matching;
* (c) two nonadjacent neighbours of `h` have no common neighbour outside `{h}`.

(a) is the tight-endpoint law of node `[9]` read at the edge `hx`: one endpoint
sits exactly at the baseline, and it is not `h`.  (b) and (c) are the two
quadrilaterals `hxyzh` and `hxzyh`, excluded because the selected object avoids
the accepted lengths and the quadrilateral is one of them -- the registered
`Data.quadrilateralAccepted`, which is where "no power-of-two cycle" enters at
its own interface.

The fact is stated of the *object*, at every high centre at once, because that
is what the manuscript proves and because a centre is data: no fact can carry
one.  Both arms of the degree split below read it. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
@[reducible] noncomputable def cubicBaselineRow
    : @AtomicStrategy (Input BranchState Presentation presentation data) _
        (instFactSystem (BranchState := BranchState)
          (Presentation := Presentation) (presentation := presentation)
          (data := data)) :=
  letI : FactSystem (Input BranchState Presentation presentation data) :=
    instFactSystem (BranchState := BranchState) (Presentation := Presentation)
      (presentation := presentation) (data := data)
  @factOnly (Input BranchState Presentation presentation data) _
    (instFactSystem (BranchState := BranchState)
      (Presentation := Presentation) (presentation := presentation)
      (data := data))
    `Hypostructure.Graph.Strategy.Spine.cubicBaseline
    { Requires := []
      Produces := [K .cubicBaseline]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun _inputs =>
      .cons (key := K .cubicBaseline)
        ⟨data.threshold_eq_three, data.dischargeScale_eq_four⟩ .nil)
    0 0

end Hypostructure.Graph.Strategy.Spine

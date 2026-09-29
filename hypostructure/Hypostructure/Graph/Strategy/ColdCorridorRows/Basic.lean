import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[147]` on an arm that already retains the exact failure of the
private-carrier rate (`[160]`'s second complement): the rate that `[146]`'s yes
arm derives from `θ < 1/78` is its literal negation on the same canonical
packing, so Core closes the pair. -/
noncomputable instance instIncompatibleRoute8RateFailsRate :
    Incompatible (Input BranchState Presentation presentation data)
      (K .route8RateFails) (K .route8Rate) where
  contradiction := fun _residual fails rate => fails.down rate.down

/-! ## Node `[155]`: G1 closes

`lem:cold-bounded-germ-trichotomy`, G1: *"Some compatible live completion and
window offset close a power-of-two cycle.  This contradicts the counterexample
condition."*  The realizing configuration's own completion is the selected
object up to the decomposition's reconstruction isomorphism, so the `[154]`
G1 arm is incompatible with the selection's target avoidance. -/
noncomputable instance instIncompatibleColdGermSomeRealizingSelection :
    Incompatible (Input BranchState Presentation presentation data)
      (K .coldGermSomeRealizing) (K .selection) where
  contradiction := fun _residual hit selected => by
    obtain ⟨germ, _active, realizing⟩ := hit.down
    exact selected.down.1 (germ.target_of_realizing
      (Graph.cycleTargetInterface data.LengthOK).isomorphismInvariant realizing)

/-! ## Node `[156]`: G2 is empty at G

`lem:cold-bounded-germ-trichotomy`, G2, read at G: "some compatible outside
context distinguishes the two representatives".  The only compatible context of
a germ's support in G is G's own surroundings `G − Z`, where the second
representative carries G's retained target response
(`BoundedGerm.sameResponse`), so no germ is distinguishing
(`BoundedGerm.not_distinguishing`).  The `[154]` G2 yes-arm is therefore empty
at G and is closed against the selection it is read on.  Lean improvement: the
G2 arm is empty at G. -/
noncomputable instance instIncompatibleColdGermSomeDistinguishingSelection :
    Incompatible (Input BranchState Presentation presentation data)
      (K .coldGermSomeDistinguishing) (K .selection) where
  contradiction := fun _residual distinguished _selected => by
    obtain ⟨germ, _active, distinguishing⟩ := distinguished.down
    exact germ.not_distinguishing distinguishing

/-! ## Node `[168]`, `lem:symmetric-pair-endpoint`

The selected occurrence retained at `[163]` is one of the nine interior
single-stub incidences of its ambient-cubic window.  The two distinct stubs of
a genuine pair force each attachment into the two-endpoint set published by
`coldWindowStubStructureRow`.  Hence the selected occurrence cannot be one of
the pair's four endpoint stubs. -/

noncomputable instance instIncompatibleTwoStrandSurvivorEndpointExclusion :
    Incompatible (Input BranchState Presentation presentation data)
      (K .coldTwoStrandSurvivor) (K .coldSymmetricPairExcluded) where
  contradiction := fun _residual survivor excluded =>
    excluded.down survivor.down

end Hypostructure.Graph.Strategy.Spine

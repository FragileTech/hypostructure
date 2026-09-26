import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Exits

/-! # Node `[109]`: the provenance of the route-`8` residual

The route-`8` residual state (`K .typeAExitSevenFree`) either sits at the
node-`[94]` silent origin of `X₀` (`K .typeASilentExitSevenFree`), or it does
not (`K .typeAExitEightNotSilent`, the exact negation at the same state).  The
silent-origin arm is closed at node `[184]` against
`lem:typeA-unified-visible-ownership`; the other arm continues through Part
IX. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[109]`, decided at the route-`8` residual state. -/
noncomputable def typeASilentExitSevenDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .typeAExitSevenFree) known]
    (silentFresh : K .typeASilentExitSevenFree ∉ known)
    (notSilentFresh : K .typeAExitEightNotSilent ∉ known) :
    Decision (K .typeASilentExitSevenFree) (K .typeAExitEightNotSilent) previous :=
  Decision.run previous (K .typeASilentExitSevenFree) (K .typeAExitEightNotSilent)
    `Hypostructure.Graph.Strategy.Spine.typeASilentExitSevenDichotomy
    (Classical.choice (show Nonempty
        ((K .typeASilentExitSevenFree).At current ⊕ (K .typeAExitEightNotSilent).At current) from by
      classical
      obtain ⟨piece, pinned, receiver, chosen, zero, state, noHandoff⟩ :=
        (previous.get (K .typeAExitSevenFree)).down
      by_cases origin : SilentExitOriginAt data.toParameters current.object piece receiver
      · exact ⟨.inl ⟨⟨piece, pinned, receiver, chosen, zero, state, noHandoff,
          origin⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, receiver, chosen, zero, state, noHandoff,
          origin⟩⟩⟩))
    silentFresh notSilentFresh

end Hypostructure.Graph.Strategy.Spine

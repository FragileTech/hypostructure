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

/-! ## Nodes `[5]`--`[7]`: the return-set form of target avoidance

Node `[6]` asks *"Mersenne return exists?"*: does some oriented edge `e` have
`R_e(G) ∩ Mers ≠ ∅`?  The yes arm is the existence of such an edge; the no arm
is its exact complement on the same object, the node-`[5]` target algebra
`R_e(G) ∩ Mers = ∅` for every oriented edge.

The yes arm closes at node `[7]`: by `lem:return-equivalence`
(`Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint`) a Mersenne return
is a power-of-two cycle, which the selection denies.  The closure is the
framework's, read off the two committed facts by `Incompatible`; the decision
itself asserts neither arm. -/

/-- **Node `[6]`: Mersenne return exists?**  The yes key is `mersenneReturn`,
the no key `returnAvoidance`; the arm not taken is absent from the taken
branch's key index. -/
noncomputable def returnAvoidanceDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    (returnFresh : K .mersenneReturn ∉ known)
    (avoidanceFresh : K .returnAvoidance ∉ known) :
    Decision (K .mersenneReturn) (K .returnAvoidance) previous :=
  Decision.run previous (K .mersenneReturn) (K .returnAvoidance)
    `Hypostructure.Graph.Strategy.Spine.returnAvoidanceDichotomy
    (Classical.choice (show Nonempty
        ((K .mersenneReturn).At current ⊕ (K .returnAvoidance).At current) from by
      by_cases exists' : ∃ dart : current.object.graph.Dart,
          ¬ Disjoint (Graph.returnLengthSet current.object dart)
            (Graph.shiftedAcceptedSet data.LengthOK)
      · exact ⟨.inl ⟨exists'⟩⟩
      · exact ⟨.inr ⟨fun dart => by
          by_contra meets
          exact exists' ⟨dart, meets⟩⟩⟩))
    returnFresh avoidanceFresh

/-- **Node `[7]`: a Mersenne return is a power-of-two cycle.**
`lem:return-equivalence` turns the yes arm of node `[6]` into an accepted cycle,
which the selection's avoidance denies. -/
noncomputable instance instIncompatibleSelectionMersenneReturn :
    Incompatible (Input BranchState Presentation presentation data)
      (K .selection) (K .mersenneReturn) where
  contradiction := fun input selection mersenne => by
    obtain ⟨dart, meets⟩ := mersenne.down
    exact meets
      ((Graph.not_hasCycleWithLength_iff_returnLengthSets_disjoint data.LengthOK
        input.object).mp selection.down.1 dart)

end Hypostructure.Graph.Strategy.Spine

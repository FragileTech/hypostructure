import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.TypeA.Support

/-! # Node `[62]`: the Type A / Type B split

`[62]` asks whether the node-`[61]` negative support `X₀` carries assigned
high-degree surplus.  The decision reads `K .negativeSupport`, fixes `X₀`
(`canonicalNegativePiece`), and splits on `σ(X₀) = 0`: the Type A arm
`K .typeALowSurplus` (node `[63]`) and the Type B arm `K .typeBHighSurplus`
(node `[64]`), exact complements at `X₀`. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- Node `[62]`, decided at `X₀`. -/
noncomputable def typeSplitDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous :
      ExactLedger (Input BranchState Presentation presentation data) current
        known)
    [FactKeys.Has (K .negativeSupport) known]
    (typeAFresh : K .typeALowSurplus ∉ known)
    (typeBFresh : K .typeBHighSurplus ∉ known) :
    Decision (K .typeALowSurplus) (K .typeBHighSurplus) previous :=
  Decision.run previous (K .typeALowSurplus) (K .typeBHighSurplus)
    `Hypostructure.Graph.Strategy.Spine.typeSplitDichotomy
    (Classical.choice (show Nonempty
        ((K .typeALowSurplus).At current ⊕ (K .typeBHighSurplus).At current) from by
      classical
      obtain ⟨piece, pinned⟩ := Graph.Contracts.TypeA.canonicalNegativePiece_isSome
        data.toParameters current.object (previous.get (K .negativeSupport)).down
      by_cases zero : current.object.ambientSurplus piece data.threshold = 0
      · exact ⟨.inl ⟨⟨piece, pinned, zero⟩⟩⟩
      · exact ⟨.inr ⟨⟨piece, pinned, Nat.pos_of_ne_zero zero⟩⟩⟩))
    typeAFresh typeBFresh

end Hypostructure.Graph.Strategy.Spine

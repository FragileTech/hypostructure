import Hypostructure.Graph.Strategy.SpineVocabulary

/-!
# Node `[115]`: some entry has `α_𝒳(ξ) ≤ 1`?

The yes key `route8SmallCoreEntry` is the existence of an indexed entry of
`Ξ(𝒳_A)` with at most one essential incidence; the no key
`route8NoSmallCoreEntry` is its exact negation on the same collection.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure.Core.Residual Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[115]`**: reads the node-`[114]` cut parity and decides whether
some entry of `𝒳_A` has `α ≤ 1`; the yes arm fixes the small-core entry
`ι₁ = canonicalRoute8SmallCoreEntry`. -/
noncomputable def route8SmallCoreCollapseRow
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger (Input BranchState Presentation presentation data)
      current known)
    [FactKeys.Has (K .route8CarrierCutParity) known]
    (smallFresh : K .route8SmallCoreEntry ∉ known)
    (noSmallFresh : K .route8NoSmallCoreEntry ∉ known) :
    Decision (K .route8SmallCoreEntry) (K .route8NoSmallCoreEntry) previous :=
  Decision.run previous (K .route8SmallCoreEntry) (K .route8NoSmallCoreEntry)
    `Hypostructure.Graph.Strategy.Spine.route8SmallCoreCollapse
    (Classical.choice (show Nonempty
        ((K .route8SmallCoreEntry).At current ⊕
          (K .route8NoSmallCoreEntry).At current) from by
      -- `[114]`, read at its last output: the cut parity of the entries of
      -- `𝒳_A` at their canonical essential carrier cores, whose cardinality
      -- `α` is tested here.
      have _parity := (previous.get (K .route8CarrierCutParity)).down
      by_cases small : Route8SmallCoreEntry data.toParameters current.object
      · exact ⟨.inl ⟨small⟩⟩
      · refine ⟨.inr ⟨?_⟩⟩
        change Route8NoSmallCoreEntry data.toParameters current.object
        dsimp only [Route8NoSmallCoreEntry]
        intro component componentMem receiver receiverMem load loadMem
          alphaSmall
        exact small ⟨component, componentMem, receiver, receiverMem, load,
          loadMem, alphaSmall⟩))
    smallFresh noSmallFresh

end Hypostructure.Graph.Strategy.Spine

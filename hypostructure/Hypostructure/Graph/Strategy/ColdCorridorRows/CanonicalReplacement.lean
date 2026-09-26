import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdNeutral

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## Node `[165]`, `lem:refined-minimality-swap`: the canonical exchange

The no-arm of `[163]` (`K .coldCanonicalNeutralConfiguration`) enters the
canonical-replacement case at node `[406]`'s marked configuration
`markedNeutralGerm?`.  If its marked representative `E` is different from the
corridor piece `Q`, gluing `E` into the retained outside context preserves the
baseline, target avoidance, vertex count, and edge count, and replaces `Q` by a
strict predecessor in the fixed canonical piece order
(`Contracts.Spine.canonicalReplacementSwap_at`, the paper's universal lemma, at
the marked configuration).  The refined-minimality contradiction belongs to
node `[166]`.
-/
@[reducible] noncomputable def canonicalReplacementSwapRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalReplacementSwap
    { Requires := [K .coldCanonicalNeutralConfiguration]
      Produces := [K .coldCanonicalReplacementSwap]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldCanonicalReplacementSwap)
        ⟨Contracts.Spine.canonicalReplacementSwap_of_neutral data.toParameters
          inputs.current.object inputs.current.baseline
          (inputs.get (K .coldCanonicalNeutralConfiguration)).down⟩
        .nil)

/-! ## Node `[166]`: refined minimality forces the trivial replacement -/

@[reducible] noncomputable def canonicalReplacementTrivialRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.canonicalReplacementTrivial
    { Requires := [K .selection, K .coldCanonicalReplacementSwap]
      Produces := [K .coldCanonicalReplacementTrivial]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldCanonicalReplacementTrivial)
        ⟨Contracts.Spine.canonicalReplacementTrivial_of_swap data.toParameters
          inputs.current.object (inputs.get (K .selection)).down
          (inputs.get (K .coldCanonicalReplacementSwap)).down⟩
        .nil)

/-! ## `lem:refined-minimality-swap`, the size split of the canonical replacement

At node `[406]`'s marked configuration (read from node `[163]`'s no-arm
`K .coldCanonicalNeutralConfiguration`), the fixed canonical order compares
sizes first: either the canonical representative of its corridor piece has
strictly fewer internal vertices — then exchanging is a strictly smaller
counterexample and the `[4]` minimality closes (node `[165]`) — or it has the
same size, which is the tie-break of node `[166]`.  Both arms are about the one
marked configuration. -/
noncomputable def canonicalSwapSizeDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
    (smallerFresh : K .coldCanonicalSwapSmaller ∉ known)
    (sameFresh : K .coldCanonicalSwapSameSize ∉ known) :
    Decision (K .coldCanonicalSwapSmaller) (K .coldCanonicalSwapSameSize) previous := by
  classical
  let neutral := (previous.get (K .coldCanonicalNeutralConfiguration)).down
  exact Decision.run previous (K .coldCanonicalSwapSmaller) (K .coldCanonicalSwapSameSize)
    `Hypostructure.Graph.Strategy.Spine.canonicalSwapSizeDichotomy
    (if smaller : ColdCanonicalSwapSmallerStatement data.toParameters
        current.object then
      .inl ⟨smaller⟩
    else
      .inr ⟨Contracts.Spine.coldCanonicalSwapSameSize_of_not_smaller
        data.toParameters current.object neutral smaller⟩)
    smallerFresh sameFresh

end Hypostructure.Graph.Strategy.Spine

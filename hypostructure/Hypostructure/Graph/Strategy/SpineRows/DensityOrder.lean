import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Contracts.Spine.DensityOrder

/-!
# The density order on the `[146]`-no arm: the combined bound, the exact size
dichotomy, and its large-arm closure

Node `[146]`'s no arm reads `θ ≥ 1/78`; the manuscript's density estimates read
`θ ≤ θ_win + o(1)` with `θ_win < 1/78` (`lem:p13-window-package` on a realized
package, `prop:p13-density` at node `[24]`).  Made exact, the two give the
single combined bound `Graph.DensityOrderBound` at G, which is false at every
order `n ≥ N₀` for the explicit cutoff `Graph.densityOrderCutoff`.  The rows
below publish the combined bound, decide `N₀ ≤ n` exactly, and close the
large arm through the framework (`Incompatible`); the small arm is the exact
residual `n < N₀`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **The realized order bound** (`[158]` yes, `[146]` no): the realized
package's entropy count and the `[146]`-no lower bound, combined at G. -/
@[reducible] noncomputable def realizedDensityOrderRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.realizedDensityOrder
    { Requires := [K .windowPackageRealized, K .windowPackageSeparated,
        K .surplusAtOrBelow, K .coldRoute8AtOrAbove, K .cubicBaseline]
      Produces := [K .realizedDensityOrder]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down.2.2.2
      .cons (key := K .realizedDensityOrder)
        ⟨Contracts.Spine.realizedDensityOrder_of_realized data.toParameters
          inputs.current.object inputs.current.baseline
          (Nat.le_of_eq (inputs.get (K .cubicBaseline)).down.1.1.symm)
          (laws.2.2.1 inputs.current.object.vertexCount)
          (inputs.get (K .windowPackageSeparated)).down.2.2.2.1
          (inputs.get (K .windowPackageRealized)).down
          (inputs.get (K .surplusAtOrBelow)).down
          (inputs.get (K .coldRoute8AtOrAbove)).down⟩
        .nil)
    0 0

/-- **The `[24]` order bound** (`[146]` no, bounded arm of `[153]`): node
`[24]`'s density cap and the `[146]`-no lower bound, combined at G. -/
@[reducible] noncomputable def boundedDensityOrderRow :
    @AtomicStrategy (Input BranchState Presentation presentation data) _
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
    `Hypostructure.Graph.Strategy.Spine.boundedDensityOrder
    { Requires := [K .densityCap, K .coldRoute8AtOrAbove, K .cubicBaseline]
      Produces := [K .boundedDensityOrder]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      let laws := (inputs.get (K .cubicBaseline)).down.2.2.2
      .cons (key := K .boundedDensityOrder)
        ⟨Contracts.Spine.boundedDensityOrder_of_densityCap data.toParameters
          inputs.current.object
          (laws.2.2.1 inputs.current.object.vertexCount)
          (inputs.get (K .densityCap)).down
          (inputs.get (K .coldRoute8AtOrAbove)).down⟩
        .nil)
    0 0

/-- **The exact size test of the realized arm**: `N₀ ≤ n` or `n < N₀`, decided
on G's order after the combined bound is published. -/
noncomputable def realizedOrderDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .realizedDensityOrder) known]
    (largeFresh : K .realizedOrderLarge ∉ known)
    (smallFresh : K .realizedOrderSmall ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .realizedOrderLarge) (K .realizedOrderSmall) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .realizedOrderLarge) (K .realizedOrderSmall)
    `Hypostructure.Graph.Strategy.Spine.realizedOrderDichotomy
    (by
      classical
      letI : FactSystem (Input BranchState Presentation presentation data) :=
        factSystem BranchState Presentation presentation data
      -- The combined bound is the predecessor; the test is on G's order.
      have _bound := (previous.get (K .realizedDensityOrder)).down
      exact if large : RealizedOrderLargeStatement data.toParameters current.object then
        .inl ⟨large⟩
      else
        .inr ⟨large⟩)
    largeFresh smallFresh

/-- **The exact size test of the `[24]` arm.** -/
noncomputable def boundedOrderDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@FactKeys.Has (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .boundedDensityOrder) known]
    (largeFresh : K .boundedOrderLarge ∉ known)
    (smallFresh : K .boundedOrderSmall ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .boundedOrderLarge) (K .boundedOrderSmall) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .boundedOrderLarge) (K .boundedOrderSmall)
    `Hypostructure.Graph.Strategy.Spine.boundedOrderDichotomy
    (by
      classical
      letI : FactSystem (Input BranchState Presentation presentation data) :=
        factSystem BranchState Presentation presentation data
      have _bound := (previous.get (K .boundedDensityOrder)).down
      exact if large : BoundedOrderLargeStatement data.toParameters current.object then
        .inl ⟨large⟩
      else
        .inr ⟨large⟩)
    largeFresh smallFresh

/-- **The realized large arm closes**: the combined bound is false at every
order past the cutoff. -/
noncomputable instance instIncompatibleRealizedDensityOrderLarge :
    Incompatible (Input BranchState Presentation presentation data)
      (K .realizedDensityOrder) (K .realizedOrderLarge) where
  contradiction := fun input bound large =>
    Graph.Contracts.Spine.realizedDensityOrder_false_of_large
      data.toParameters input.object bound.down large.down

/-- **The `[24]` large arm closes.** -/
noncomputable instance instIncompatibleBoundedDensityOrderLarge :
    Incompatible (Input BranchState Presentation presentation data)
      (K .boundedDensityOrder) (K .boundedOrderLarge) where
  contradiction := fun input bound large =>
    Graph.Contracts.Spine.boundedDensityOrder_false_of_large
      data.toParameters input.object bound.down large.down

end Hypostructure.Graph.Strategy.Spine

import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.ColdIncrementArithmetic
import Hypostructure.Graph.ColdGermFamily
import Hypostructure.Graph.Strategy.ColdCorridorRows.Basic
import Hypostructure.Graph.Contracts.Spine.ColdMass

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-! ## The route-8 rate failure, `rem:route8-carrier-margin` read exactly

When the private-carrier rate `τ < 3/13` of node `[120]` fails on a residual that
already carries the hot/cold ledger of the fixed packing, the manuscript's
delicate density interval (row 2 of `tab:cold-branch-ledger`) is handled by the
hot/cold pass; in exact form its residue is decided by the cold family: if the
cold family is nonempty, the failure is carried by cold windows whose selected
corridors are charged as in `[174]`--`[177]` (absorbed germs or genuine germs);
if it is empty, every packed window is hot at the exact skeleton budget and the
rate still fails — the exact budget-edge corner.  This is that decision on the
literal residual. -/
noncomputable def coldFamilyDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : FactKeys (Input BranchState Presentation presentation data)}
    (previous : ExactLedger
      (Input BranchState Presentation presentation data) current known)
    [FactKeys.Has (K .hotColdPartition) known]
    (positiveFresh : K .coldFamilyPositive ∉ known)
    (emptyFresh : K .coldFamilyEmpty ∉ known) :
    Decision (K .coldFamilyPositive) (K .coldFamilyEmpty) previous := by
  classical
  exact Decision.run previous (K .coldFamilyPositive) (K .coldFamilyEmpty)
    `Hypostructure.Graph.Strategy.Spine.coldFamilyDichotomy
    (if positive : 0 < (canonicalColdWindows data.toParameters current.object).card then
      .inl ⟨positive⟩
    else
      .inr ⟨Nat.eq_zero_of_not_pos positive⟩)
    positiveFresh emptyFresh

/-! ## `thm:cold-branch-quantitative-closure`: no terminal cold residual

With the germs routed and the table closed, no local terminal cold pattern
remains on this residual: the branch is closed by routing, exactly as the
manuscript's Part XI leaves are drawn. -/
@[reducible] noncomputable def coldBranchClosedRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.coldBranchClosed
    { Requires := [K .coldGermRouted, K .coldSameInterfaceTable]
      Produces := [K .coldBranchClosed]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .coldBranchClosed)
        ⟨Contracts.Spine.coldBranchClosed_of_routing data.toParameters
          inputs.current.object
          (inputs.get (K .coldGermRouted)).down
          (inputs.get (K .coldSameInterfaceTable)).down⟩
        .nil)

/-! ## Node `[24]`: `prop:p13-density`, after the cold branch

The manuscript's `[24]` reads "bounded cold-mass return from [153]:
`θ ≤ θ_win + o(1)`; high entropy: `θ ≤ 0.01198542083…`".  On the `[153]` bounded arm the cold mass is
`C ≤ (1 + (threshold+1)·B_cold)·σ(G)`; with
`lem:hot-failure-cold-mass` (`K .coldMass`,
`bitRate·|𝒫| ≤ bitRate·C + allowance`) and the near-cubic surplus bound
`σ(G) ≤ T(n)` (`K .coldAmbientCubic`) this is the manuscript's window-only
density cap with its exact `o(1)`. -/
@[reducible] noncomputable def densityBudgetRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.finiteDensityBudget
    { Requires := [K .coldMass, K .coldMassBounded, K .coldAmbientCubic,
        K .hotColdPartition]
      Produces := [K .densityCap]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .densityCap)
        ⟨Contracts.Spine.densityCap_of_coldMassBounded data.toParameters
          inputs.current.object data.five_le_windowOrder
          (inputs.get (K .coldMass)).down
          (inputs.get (K .coldMassBounded)).down
          (inputs.get (K .coldAmbientCubic)).down
          (inputs.get (K .hotColdPartition)).down⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine

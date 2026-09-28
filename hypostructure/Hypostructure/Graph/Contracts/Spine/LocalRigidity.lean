import Hypostructure.Graph.Statements.LocalRigidity

/-!
# Contracts: local rigidity of G

Proof-agnostic contract lemmas for `Statements/LocalRigidity.lean`.  Each is
stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter; its hypotheses are exactly ledger facts (or their projections): the
selection's target avoidance and the presentation's dyadic length law.  The
canonical packing `P₀` is a valid window packing by its definition
(`canonicalWindowPacking_spec`).  One contract per statement:
`<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.LocalRigidity

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

theorem threeRouteFan_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ThreeRouteFanStatement object :=
  Graph.LocalRigidity.threeRouteFan avoid lengthLaw

theorem threeRouteChain_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    ThreeRouteChainStatement object :=
  Graph.LocalRigidity.threeRouteChain avoid lengthLaw

theorem windowAttachmentGap_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    WindowAttachmentGapStatement data object :=
  ⟨Graph.LocalRigidity.crossGap avoid lengthLaw,
    Graph.LocalRigidity.windowAttachmentRules avoid lengthLaw
      (canonicalWindowPacking_spec data object).1⟩

theorem windowPositionStubs_holds :
    WindowPositionStubsStatement data object :=
  Graph.LocalRigidity.windowPositionStubs (canonicalWindowPacking_spec data object).1

end Hypostructure.Graph.Contracts.Spine.LocalRigidity

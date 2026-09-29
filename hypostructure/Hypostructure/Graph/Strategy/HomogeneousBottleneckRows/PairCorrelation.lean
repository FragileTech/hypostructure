import Hypostructure.Graph.Strategy.SpineVocabulary
import Hypostructure.Graph.Strategy.HomogeneousBottleneckRows.Basic
import Hypostructure.Graph.Contracts.SurplusPair.PairCorrelation
import Hypostructure.Graph.Contracts.SurplusPair.PairCoverage
import Hypostructure.Graph.Contracts.SurplusPair.PairUncrossing

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

/-- **Node `[178]`, the correlation mass of G's canonical overlap system.**

Reads the canonical overlap system and publishes the exact signature counts of
the canonical exposure order of the failed prefix, the mass identity
`2^{b+t} ≤ |class| + mass`, and the first non-branching index of the count
failure. -/
@[reducible] noncomputable def pairCorrelationRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairCorrelation
    { Requires := [K .pairOverlapSystem]
      Produces := [K .pairCorrelation]
      requiresUnique := by simp
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairCorrelation)
        ⟨Graph.Contracts.SurplusPair.pairCorrelation_of_overlapSystem
          (inputs.get (K .pairOverlapSystem)).down⟩
        .nil)

/-- **Nodes `[179]`--`[180]`, coverage decided at G.**

Reads G's canonical return system, the selection (G avoids the target), the
replacement exclusion and the dyadic length law.  The target cycle, the target
defect and the compression alternatives of `[179]` and `[180]` are empty at G,
and the arithmetic input of `[180]` would produce an accepted cycle of G, so
coverage is exactly the Type B handoff or the serial system. -/
@[reducible] noncomputable def pairCoverageRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairCoverage
    { Requires := [K .pairDemandReturns, K .selection, K .replacementExclusion,
        K .cubicBaseline]
      Produces := [K .pairCoverage]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairCoverage)
        ⟨Graph.Contracts.SurplusPair.pairCoverage_of_demandReturns
          (inputs.get (K .pairDemandReturns)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1
          (inputs.get (K .replacementExclusion)).down⟩
        .nil)

/-- **Node `[180]`, the full-modulus arithmetic of G's canonical serial system.**

The canonical full-modulus data of the serial system (frequent increments, their
gcd, the canonical smear, the Frobenius-filled central range) cannot satisfy every
arithmetic test at G: it would realize a power of two, an accepted cycle. -/
@[reducible] noncomputable def pairFullModulusRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairFullModulus
    { Requires := [K .pairSerialDemandSystem, K .selection, K .cubicBaseline]
      Produces := [K .pairFullModulus]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairFullModulus)
        ⟨Graph.Contracts.SurplusPair.pairFullModulus_of_serial
          (inputs.get (K .pairSerialDemandSystem)).down
          (inputs.get (K .selection)).down.1
          (inputs.get (K .cubicBaseline)).down.2.1.2.1⟩
        .nil)

/-- **Node `[179]`, the uncrossing of G's canonical connector routes.**

Reads G's canonical return system and the selection.  The two oriented routes of the
obstruction's connector are paths of G; disjoint routes close with the two demand
edges into a cycle, and crossing routes are rerouted at their first and last common
vertex into two paths that close with the demand edges.  Every closing length is one
or not accepted. -/
@[reducible] noncomputable def pairUncrossingRow :
    AtomicStrategy (Input BranchState Presentation presentation data) :=
  factOnly `Hypostructure.Graph.Strategy.Spine.pairUncrossing
    { Requires := [K .pairDemandReturns, K .selection]
      Produces := [K .pairUncrossing]
      requiresUnique := by key_fresh
      producesUnique := by simp
      producesNonempty := by simp }
    (fun inputs =>
      .cons (key := K .pairUncrossing)
        ⟨Graph.Contracts.SurplusPair.pairUncrossing_of_demandReturns
          (inputs.get (K .pairDemandReturns)).down
          (inputs.get (K .selection)).down.1⟩
        .nil)

end Hypostructure.Graph.Strategy.Spine

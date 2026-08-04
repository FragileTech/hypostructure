import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.ReceiverLoad
import Hypostructure.Core.DyadicLength
import HypostructureErdos64EG.OfficialStatement

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-!
# EG problem and target registration

The application boundary exposes one Core problem and one Core target, and
nothing else.  Every law relating them -- the bridge between the packed cycle
target and the pinned public statement, the isomorphism invariance of the
baseline, and the transport of the target through it -- is owned by
`Hypostructure.Graph.MinimumDegreeCycleTarget`.
-/

/-- Receiver/load parameters are part of the problem presentation.  They are
not strategy-local constants: Core carries them in `Problem.presentation`.
Other graph problems can provide a different profile or a richer presentation
state through the same field.

`remainderEntropyThresholdDenominator := 10` is the manuscript's own
two-budget threshold: node [50] asks `η(R) ≥ (1/10)·log₂ n` for the
per-vertex skeleton entropy `η(R) = log₂|𝒢(R)|/|R|` of
`def:remainder-entropy`, and `prop:two-budget` splits its branches on exactly
that comparison, the high-entropy branch (a) computing
`2^{η(R)|R|} ≥ n^{|R|/10}`.  It is a proof-design threshold chosen by the
argument, not a quantity measured from a graph, so it is declared here with
the other presentation parameters instead of appearing as a literal inside a
strategy registration. -/
def erdosReceiverLoadProfile :
    Graph.ReceiverLoad.LoadCapacityProfile where
  baselineDegree := 3
  loadMultiplier := 4
  remainderEntropyThresholdDenominator := 10
  dischargeRate_gt := by norm_num
  dischargeRate_le := by norm_num

/-- The sole baseline hypothesis in the official theorem, with its threshold
read from the registered problem presentation. -/
abbrev Baseline (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.MinimumDegreeAtLeast erdosReceiverLoadProfile.baselineDegree object

def BranchState (_object : Graph.FiniteObject.{u}) : Type := Unit

/-- The minimal domain-neutral problem registration for Problem 64.
It is transparent so Graph-owned canonical capabilities are inferred from
the constructor rather than re-registered by the application. -/
abbrev problem : Core.Problem :=
  Graph.problemWithPresentation Baseline BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile

/-! The public theorem proposition is registered beside the Core problem
contract.  Core keeps targets separate from `Problem`; this alias is the
application boundary consumed by strategy-level terminal proofs. -/
abbrev officialStatement : Prop := OfficialStatement.{u}

/-! The accepted cycle lengths are the framework's executable dyadic length
family; the manuscript's `2^k`, `k ≥ 2` is that predicate at every occurrence
below. -/
export Hypostructure.Core.DyadicLength (PowerOfTwoLength powerOfTwoLength_iff)

/-- A packed graph realizes the target when it has an accepted Mathlib cycle. -/
def Target (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HasCycleWithLength PowerOfTwoLength object

/-! The single public target contract consumed by strategy code.  Its
`Statement` is the pinned `OfficialStatement` and its `Predicate` is `Target`;
both bridge directions are the framework's. -/
def target : Core.Target problem :=
  Graph.minimumDegreeCycleTarget erdosReceiverLoadProfile.baselineDegree
    BranchState
    Graph.ReceiverLoad.LoadCapacityProfile erdosReceiverLoadProfile
    PowerOfTwoLength (fun exponent => exponent ≥ 2) (fun exponent => 2 ^ exponent)
    powerOfTwoLength_iff

end HypostructureErdos64EG

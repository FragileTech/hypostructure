import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.FiniteBarrierEnumeration
import Hypostructure.Core.Strategy.FiniteDensityBudgetSemantics
import Hypostructure.Core.Strategy.ColdBranchAggregationSemantics

/-!
# Finite density budget

This domain-neutral Strategy compares the exact multiplicative state demand
of a retained finite packing with the exact represented ambient capacity.
All three inputs are typed reads from the literal predecessor ledger:

* the retained packing cardinality;
* the safe/flat products computed by a prior finite barrier enumeration;
* the represented ambient-state cardinality.

The Strategy does not reconstruct any producer.  CT14 performs the sole
exhaustive comparison and appends its routed result to the predecessor.
-/

namespace Hypostructure.Core.Strategy.FiniteDensityBudget

open Hypostructure
open Hypostructure.Core.Residual

universe u

/-- Exact predecessor queries required by the generic multiplicative budget.
The values are not registration fields: Core constructs these queries from
the actual producer entries and preserves them through intervening ledger
extensions. -/
structure Profile (Previous : Type u) where
  packingCount : Query Previous fun _ => Nat
  barrierSummary : Query Previous fun _ =>
    FiniteBarrierEnumeration.Summary
  ambientCapacity : Query Previous fun _ => Nat
  ambientCapacity_pos : Query Previous fun previous =>
    0 < ambientCapacity previous
  /-- The compared `Summary` is Core-derived, so its `binaryRateFloor` really is
  a `log₂` of its own columns.  Produced at the barrier node; never a field a
  registration could fill. -/
  barrierDerived : Query Previous fun previous =>
    FiniteBarrierEnumeration.Summary.Derived (barrierSummary previous)
  /-- The compared `Summary`'s flat column is nonvanishing, as proved and
  published inside the sealed barrier strategy. -/
  barrierFlatPositive : Query Previous fun previous =>
    0 < (barrierSummary previous).flatProduct
  /-- **`def:near-cubic-spine`, the node-`[19]` at-or-below branch load and
  table value this node was entered under.**  Not a registration field: Core
  reads it off the literal `scaleThresholdDichotomy` branch payload that
  routed into this node, exactly as `barrierSummary` is read off the barrier
  node's own payload. -/
  degreeSurplusLoad : Query Previous fun _ => Nat
  degreeSurplusThreshold : Query Previous fun _ => Nat
  /-- The node-`[19]` at-or-below comparison itself. -/
  nearCubic : Query Previous fun previous =>
    degreeSurplusLoad previous ≤ degreeSurplusThreshold previous

/-- Lift the sole inert residual observable while retaining the
producer-owned ledger queries verbatim.  The barrier facts arrive together with
the `Summary` they are about, as the barrier node's own
`FiniteBarrierEnumeration.RateLedger`, so no consumer restates them.  The
near-cubic-spine facts arrive the same way, as the node-`[19]` branch's own
retained load/table/comparison -- not chosen or re-derived here. -/
def Profile.ofRegistration
    {Residual : Type u} [HasResidual Previous Residual]
    (packingCount : Query Previous fun _ => Nat)
    (barrierRate : FiniteBarrierEnumeration.RateLedger Previous)
    (registration : Registration Residual)
    (degreeSurplusLoad degreeSurplusThreshold : Query Previous fun _ => Nat)
    (nearCubic : Query Previous fun previous =>
      degreeSurplusLoad previous ≤ degreeSurplusThreshold previous) :
    Profile Previous where
  packingCount := packingCount
  barrierSummary := barrierRate.summary
  ambientCapacity :=
    (Query.residual (Source := Previous) (Residual := Residual)).map
      fun _ residual => registration.ambientCapacity residual
  ambientCapacity_pos :=  fun previous =>
    registration.ambientCapacity_pos (residualOf previous)
  barrierDerived := barrierRate.derived
  barrierFlatPositive := barrierRate.flatPositive
  degreeSurplusLoad := degreeSurplusLoad
  degreeSurplusThreshold := degreeSurplusThreshold
  nearCubic := nearCubic

namespace Profile

variable (profile : Profile Previous)

def stateDemand (previous : Previous) : Nat :=
  let summary := profile.barrierSummary previous
  summary.safeProduct ^ profile.packingCount previous

def representedCapacity (previous : Previous) : Nat :=
  let summary := profile.barrierSummary previous
  summary.flatProduct ^ profile.packingCount previous *
    profile.ambientCapacity previous

def canonicalMembers : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

def members (Previous : Type u) :
    Query Previous fun _ => Core.Finite.Enumeration Unit :=
   fun _ => canonicalMembers

def spec : CT14.Spec Previous where
  Member := fun _ => Unit
  Label := fun _ => Unit
  memberLowerMass := fun previous _ => profile.stateDemand previous
  memberCapacity := fun previous _ =>
    some (profile.representedCapacity previous)
  memberLabel := fun _ _ => some ()

def workCoefficient : Nat :=
  CT14.localCheckBound canonicalMembers

def workDegree : Nat :=
  Fintype.card Unit

theorem workBound (previous : Previous) :
    CT14.localCheckBound ((members Previous) previous) ≤
      workCoefficient *
        (((members Previous) previous).card + 1) ^ workDegree := by
  simp only [members, workCoefficient, workDegree,
    Fintype.card_unit, Nat.pow_one]
  exact Nat.le_mul_of_pos_right _
    (by omega : 0 < canonicalMembers.card + 1)

def capability : CT14.Capability profile.spec where
  members := members Previous
  labelDecidableEq := fun _ => inferInstanceAs (DecidableEq Unit)
  inputSize := fun previous => ((members Previous) previous).card
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/-- The sole executable object: Core's canonical CT14 adapter. -/
noncomputable def execution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct14 profile.capability

/-- Strict multiplicative overflow, retaining CT14's literal result. -/
structure OverflowResidual (previous : Previous) where
  result : CT14.ExecutionResult profile.spec profile.capability
  previous_eq : result.stage.previous = previous
  selected : result.terminal = .aggregate

/-- Complementary multiplicative density cap, retaining CT14's literal
result. -/
structure CapResidual (previous : Previous) where
  result : CT14.ExecutionResult profile.spec profile.capability
  previous_eq : result.stage.previous = previous
  selected : result.terminal = .capacity

inductive RoutedResidual (previous : Previous) where
  | overflow (residual : profile.OverflowResidual previous)
  | cap (residual : profile.CapResidual previous)

private theorem noUnbounded (previous : Previous)
    (residual : CT14.UnboundedMemberResidual
      profile.capability previous) : False := by
  have impossible := residual.holds
  simp [spec] at impossible

private theorem noMissingLabel (previous : Previous)
    (residual : CT14.MissingLabelResidual
      profile.capability previous) : False := by
  have impossible := residual.holds
  simp [spec] at impossible

/-- Eliminate only CT14 terminals made impossible by total capacity and label
semantics.  The overflow/cap comparison is executed exactly once by CT14. -/
noncomputable def route (previous : Previous) :
    profile.RoutedResidual previous :=
  let result := profile.execution.run previous
  by
    cases terminalEq : result.terminal with
    | unboundedMember =>
        have outcome : CT14.Outcome profile.capability result.stage.previous
            .unboundedMember := by
          simpa [terminalEq] using result.outcome
        cases outcome with
        | unboundedMember _ residual =>
            exact (profile.noUnbounded result.stage.previous residual).elim
    | missingLabel =>
        have outcome : CT14.Outcome profile.capability result.stage.previous
            .missingLabel := by
          simpa [terminalEq] using result.outcome
        cases outcome with
        | missingLabel _ _ residual =>
            exact
              (profile.noMissingLabel result.stage.previous residual).elim
    | aggregate =>
        exact .overflow ⟨result, rfl, terminalEq⟩
    | capacity =>
        exact .cap ⟨result, rfl, terminalEq⟩

/-- Standard Core dichotomy view of the exact CT14 route. -/
noncomputable def dichotomy : Core.Strategy.Dichotomy Previous where
  LeftPayload := profile.OverflowResidual
  RightPayload := profile.CapResidual
  classify := fun previous =>
    match profile.route previous with
    | .overflow residual => .inl residual
    | .cap residual => .inr residual

def OverflowResidual.outcome
    {previous : Previous} (residual : profile.OverflowResidual previous) :
    CT14.Outcome profile.capability previous .aggregate := by
  rw [← residual.previous_eq]
  simpa [residual.selected] using residual.result.outcome

/-- A strict density overflow cannot arise from an empty packing.  The proof
uses the literal CT14 inequality and the positivity law of the represented
ambient state space; it does not inspect or reconstruct the packing. -/
theorem OverflowResidual.packingCount_pos
    {previous : Previous}
    (residual : profile.OverflowResidual previous) :
    0 < profile.packingCount previous := by
  have overflow : profile.representedCapacity previous <
      profile.stateDemand previous := by
    cases outcomeEq : residual.outcome with
    | aggregate ledger certificate =>
        have exactComparison := certificate
        change ledger.capacity.total < ledger.lower.total at exactComparison
        rw [ledger.capacity.total_exact, ledger.lower.total_exact] at exactComparison
        simpa [stateDemand, representedCapacity, CT14.upperCapacity,
          CT14.capacityEntries, CT14.lowerMass, CT14.lowerMassEntries,
          CT14.Capability.membersAt, capability, members, canonicalMembers,
          Core.Finite.Enumeration.singleton,
          Core.Finite.Enumeration.ofNodupList, spec] using exactComparison
  by_contra notPositive
  have packingZero : profile.packingCount previous = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  have capacityAtLeastOne : 1 ≤ profile.ambientCapacity previous :=
    profile.ambientCapacity_pos previous
  have capacityLessOne : profile.ambientCapacity previous < 1 := by
    simpa [stateDemand, representedCapacity, packingZero] using overflow
  exact (Nat.not_lt_of_ge capacityAtLeastOne) capacityLessOne

/-- Query-only interface to the exact selected overflow ledger entry. -/
noncomputable def overflowLedger (profile : Profile Previous) :
    ColdBranchAggregation.OverflowLedger profile.dichotomy.LeftStage :=
  let selected : Query profile.dichotomy.LeftStage fun stage =>
      profile.OverflowResidual stage.previous :=
    Query.latest
  { lowerMass := selected.map fun _ residual =>
      match residual.outcome with
      | .aggregate ledger _ => ledger.lower.total
    capacity := selected.map fun _ residual =>
      match residual.outcome with
      | .aggregate ledger _ => ledger.capacity.total
    overflow :=  fun stage =>
      let residual := selected stage
      match outcomeEq : residual.outcome with
      | .aggregate _ certificate => by
          simpa [residual, outcomeEq] using certificate }

def CapResidual.outcome
    {previous : Previous} (residual : profile.CapResidual previous) :
    CT14.Outcome profile.capability previous .capacity := by
  rw [← residual.previous_eq]
  simpa [residual.selected] using residual.result.outcome

/-- The literal cap inequality retained on the surviving density branch: the
exact multiplicative state demand really does fit inside the represented
ambient capacity.

This is the complementary-terminal mirror of the strict overflow inequality
that `OverflowResidual.packingCount_pos` extracts, and it is the entire
mathematical content the cap residual carries.  Written out, it is

  `safeProduct ^ packingCount ≤ flatProduct ^ packingCount * ambientCapacity`,

which is `lem:skeleton-dominates` applied to the retained finite packing: the
window package's own state demand never outruns the labelled skeleton budget
on the branch that survived.  It is proved from CT14's own aggregate ledger,
so no producer is reconstructed and no numeral is assumed. -/
theorem CapResidual.stateDemand_le_representedCapacity
    {previous : Previous} (residual : profile.CapResidual previous) :
    profile.stateDemand previous ≤ profile.representedCapacity previous := by
  cases outcomeEq : residual.outcome with
  | capacity ledger bound =>
      have exactComparison := bound
      change ledger.lower.total ≤ ledger.capacity.total at exactComparison
      rw [ledger.capacity.total_exact, ledger.lower.total_exact]
        at exactComparison
      simpa [stateDemand, representedCapacity, CT14.upperCapacity,
        CT14.capacityEntries, CT14.lowerMass, CT14.lowerMassEntries,
        CT14.Capability.membersAt, capability, members, canonicalMembers,
        Core.Finite.Enumeration.singleton,
        Core.Finite.Enumeration.ofNodupList, spec] using exactComparison

/-- **The entropy form of the surviving density cap.**

`stateDemand_le_representedCapacity` is a comparison of two products.  Taking
`log₂` of it is the manuscript's `[22]`–`[24]` comparison

  `rate · packingCount ≤ log₂ (ambient capacity)`,

and this is that statement in exact `Nat` form, with no rounding and no `o(·)`
term: `2 ^ (rate · packingCount) ≤ ambientCapacity`.

`rate` is not a numeral and is not chosen here.  It is whatever per-package
rate the ledger's own barrier `Summary` certifies through `rateFloor` — for a
package declared at every separated dyadic scale of the residual object, that
is the registered table's rate times the object's scale count, so the left
side really is `c_hot · log₂ n · p₁₃` bits and it grows with the residual.

Nothing is reconstructed: `rateFloor` and `flatPositive` are facts about the
`Summary` already on the ledger, and the cap itself is CT14's retained
capacity ledger. -/
theorem CapResidual.two_pow_rate_mul_packingCount_le_ambientCapacity
    {previous : Previous} (residual : profile.CapResidual previous)
    {rate : Nat}
    (rateFloor :
      2 ^ rate * (profile.barrierSummary previous).flatProduct ≤
        (profile.barrierSummary previous).safeProduct)
    (flatPositive :
      0 < (profile.barrierSummary previous).flatProduct) :
    2 ^ (rate * profile.packingCount previous) ≤
      profile.ambientCapacity previous := by
  have cap := residual.stateDemand_le_representedCapacity
  set packing := profile.packingCount previous with packingDef
  set flat := (profile.barrierSummary previous).flatProduct with flatDef
  set safe := (profile.barrierSummary previous).safeProduct with safeDef
  have capExact : safe ^ packing ≤ flat ^ packing *
      profile.ambientCapacity previous := by
    simpa [stateDemand, representedCapacity, safeDef, flatDef, packingDef]
      using cap
  have raised : (2 ^ rate * flat) ^ packing ≤ safe ^ packing :=
    Nat.pow_le_pow_left rateFloor _
  rw [mul_pow, ← pow_mul] at raised
  have chain : 2 ^ (rate * packing) * flat ^ packing ≤
      flat ^ packing * profile.ambientCapacity previous :=
    le_trans raised capExact
  rw [mul_comm (flat ^ packing)] at chain
  exact Nat.le_of_mul_le_mul_right chain (Nat.pow_pos flatPositive)

/-- **Query-only interface to the exact selected cap ledger entry.**

The complementary-terminal mirror of `overflowLedger`.  The overflow branch
publishes its strict inequality; until now the *surviving* branch published
nothing, so the one fact the whole near-cubic continuation is built on --
`lem:skeleton-dominates` applied to the retained window package -- was
discarded at exactly the node where the proof continues.

Every field is a preserved producer query, and the cap itself is
`CapResidual.stateDemand_le_representedCapacity`, i.e. CT14's own retained
capacity ledger.  No producer is reconstructed and no numeral is assumed. -/
noncomputable def capLedger (profile : Profile Previous) :
    CapLedger profile.dichotomy.RightStage :=
  let selected : Query profile.dichotomy.RightStage fun stage =>
      profile.CapResidual stage.previous :=
    Query.latest
  { packingCount := profile.packingCount.preserve
    barrierSummary := profile.barrierSummary.preserve
    ambientCapacity := profile.ambientCapacity.preserve
    cap :=  fun stage =>
      (selected stage).stateDemand_le_representedCapacity
    entropyCap :=  fun stage => by
      change 2 ^ ((profile.barrierSummary stage.previous).binaryRateFloor *
        profile.packingCount stage.previous) ≤
        profile.ambientCapacity stage.previous
      rcases (profile.barrierDerived stage.previous).two_pow_binaryRateFloor_mul_flatProduct_le_or_eq_zero with
        rateFloor | rateZero
      · simpa using
          (selected stage).two_pow_rate_mul_packingCount_le_ambientCapacity
            (profile := profile) rateFloor
            (profile.barrierFlatPositive stage.previous)
      · have h := profile.ambientCapacity_pos stage.previous
        simp only [rateZero, Nat.zero_mul, pow_zero]
        exact Nat.succ_le_iff.mpr h
    ambientCapacity_pos := profile.ambientCapacity_pos.preserve
    barrierDerived := profile.barrierDerived.preserve
    barrierFlatPositive := profile.barrierFlatPositive.preserve
    degreeSurplusLoad := profile.degreeSurplusLoad.preserve
    degreeSurplusThreshold := profile.degreeSurplusThreshold.preserve
    nearCubic := profile.nearCubic.preserve }

end Profile

end Hypostructure.Core.Strategy.FiniteDensityBudget

import Hypostructure.Graph.Statements.CanonicalSurplusCode

/-!
# Statements: the entropy counts `[131]`/`[137]` and the pair-code chain `[178]`--`[182]`, at G

Every statement is about G's canonical objects (`Statements/CanonicalSurplusCode`,
`Statements/CanonicalSurplus`, `Statements/CanonicalSurplusCapacity`): the
node-`[129]` spine family, G's canonical pair-response activation, G's
canonical capacity presentation, and the canonical pair-code chain built on
them.  Each branch test is the paper predicate at the one pinned witness, and
its no arm is the literal negation.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-! ## Node `[131]`: the free-pair entropy count -/

/-- **Node `[131]`, `prop:sparse-entropy-sandwich`'s entropy count at G**
(tex 4931-4983): the mixed family of G's node-`[129]` spine family and G's full
pair-response family `ℛ_Π` at its canonical activation realizes its code among
the labelled skeletons of G, `2^{|ℐ_spine| + |ℛ_Π|} ≤ C(N,m)`. -/
def FreePairEntropySandwichStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ activation spine,
    canonicalPairActivation data object = some activation ∧
    canonicalBaselineSpineFamily data object = some spine ∧
    2 ^ (spine.family.card +
        (activation.pairFamily (codeSchedule data object)).card) ≤
      Graph.skeletonBudget object

/-- Node `[131]`, count fails: the negation of the free-pair entropy count. -/
noncomputable abbrev FreePairCountFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ FreePairEntropySandwichStatement data object

/-- **Node `[131]`, count fails, input of `[178]`** (tex 5046-5058): at G's
canonical activation, with no blocked pair on the full schedule (all six
clauses of `def:surplus-blockers`), and at the canonical
realization of G's spine family's code, the count fails on the literal
schedule. -/
def FreePairCodeUnrealizedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ activation spine realization,
    canonicalPairActivation data object = some activation ∧
    canonicalBaselineSpineFamily data object = some spine ∧
    canonicalBaselineRealizationAt object spine = some realization ∧
    ¬ Graph.HasSparsePairBlocker
        (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK) activation (codeSchedule data object) ∧
    (codeSchedule data object).card = (object.degreeSurplus data.threshold).choose 2 ∧
    ¬ 2 ^ (spine.family.card + (codeSchedule data object).card) ≤
      Graph.skeletonBudget object ∧
    (codeSchedule data object).Nonempty

/-! ## Node `[137]`: the free-side entropy count -/

/-- **Node `[137]`'s input** (`prop:sparse-entropy-sandwich-with-blockers`,
tex 4985-4995): G's canonical capacity presentation (node `[136]`), G's
node-`[129]` spine family, and the schedule count `|Π(𝒜₀)| = C(σ,2)`. -/
def BlockedPairEntropySetupStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ capacity spine,
    canonicalCapacity data object = some capacity ∧
    canonicalBaselineSpineFamily data object = some spine ∧
    (codeSchedule data object).card = (object.degreeSurplus data.threshold).choose 2

/-- **Node `[137]`, `prop:sparse-entropy-sandwich-with-blockers`'s count at G**
(tex 4985-5044): the mixed family of G's spine family and the free side of G's
canonical capacity charge realizes its code among the labelled skeletons of G. -/
def BlockedPairEntropySandwichStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ capacity, canonicalCapacity data object = some capacity ∧
    ∃ spine, canonicalBaselineSpineFamily data object = some spine ∧
      2 ^ (spine.family.card +
          (Graph.freeSide object.vertexPairDecidableEq
            (object.portPairSchedule data.threshold)
            capacity.tokenOrder capacity.Eligible
            capacity.eligibleDecidable).card) ≤
        Graph.skeletonBudget object

/-- Node `[137]`, count fails on the free side of the capacity charge. -/
noncomputable abbrev BlockedPairCountFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ BlockedPairEntropySandwichStatement data object

/-- **Node `[137]`, count fails on the free side, input of `[178]`**: at G's
canonical capacity presentation and the canonical realization of G's spine
family's code, the count fails on the free side. -/
def BlockedPairCodeUnrealizedStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ capacity spine realization,
    canonicalCapacity data object = some capacity ∧
    canonicalBaselineSpineFamily data object = some spine ∧
    canonicalBaselineRealizationAt object spine = some realization ∧
    (codeSchedule data object).card = (object.degreeSurplus data.threshold).choose 2 ∧
    ¬ 2 ^ (spine.family.card + (codeFreeSide data object capacity).card) ≤
      Graph.skeletonBudget object ∧
    (codeFreeSide data object capacity).Nonempty

/-! ## Node `[178]` -/

/-- **Node `[178]`, the first failure of G's pair code**: the canonical first
failed extension exists. -/
def PairOverlapFirstFailureStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ first, canonicalPairFirstFailure data object = some first

/-- **Node `[178]`, `def:pair-overlap-system` at G**: the canonical overlap
system of the canonical first failure exists. -/
def PairOverlapSystemStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ system, canonicalPairOverlapSystem data object = some system

/-- **Node `[178]`, the conditional-factorization test**, at G's canonical
overlap system. -/
def PairConditionalFactorizationStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ system, canonicalPairOverlapSystem data object = some system ∧
    system.ConditionalFactorization

/-- Node `[178]`, no factorization: the negation of the test. -/
noncomputable abbrev PairFactorizationFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ PairConditionalFactorizationStatement data object

/-- **Node `[178]`, `lem:pair-failure-overlap` at G**: the canonical minimal
overlap obstruction of the canonical overlap system exists. -/
def PairFailureOverlapStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ overlap, canonicalPairFailureOverlap data object = some overlap

/-! ## Node `[179]` -/

/-- **Node `[179]`**: the two demands of the canonical obstruction's failed
pair, their canonical returns, and `ℓ_ret`. -/
def PairDemandReturnsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns

/-- **Node `[179]`, the coverage test of `lem:pair-system-realizability`** for
G's canonical return system (tex 5139-5143). -/
def PairSystemRealizabilityStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    Nonempty (PairSystemRealizabilityOutcome returns)

/-- Node `[179]`, no exhaustive uncrossing: at G's canonical return system the
coverage test fails (its literal negation at the same pinned returns). -/
def PairRealizabilityFailsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ¬ Nonempty (PairSystemRealizabilityOutcome returns)

/-- **Node `[179]`, alternatives (i)--(iv)** (`lem:pair-system-realizability`,
tex 5110-5130, listed before (v)): one of the already-routed alternatives
occurs for G's canonical return system. -/
def PairSystemEarlyOutcomeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    Nonempty (PairSystemEarlyOutcome returns)

/-- Node `[179]`, serial arm: none of (i)--(iv) occurs for G's canonical return
system (the literal negation at the same pinned returns). -/
def PairSystemNoEarlyOutcomeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ returns, canonicalPairDemandReturns data object = some returns ∧
    ¬ Nonempty (PairSystemEarlyOutcome returns)

/-- **Node `[179]`, alternative (v)**: G's canonical serial demand system. -/
def PairSerialDemandSystemStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ serial, canonicalPairSerialSystem data object = some serial

/-! ## Node `[180]` -/

/-- **Node `[180]`, the coverage test of
`lem:pair-system-increment-arithmetic`** for G's canonical serial system. -/
def PairIncrementCoveredStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ serial, canonicalPairSerialSystem data object = some serial ∧
    Nonempty (PairIncrementOutcome serial)

/-- Node `[180]`, uncovered increment response: at G's canonical serial system
the coverage test fails (its literal negation at the same pinned system). -/
def PairIncrementFailsStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ serial, canonicalPairSerialSystem data object = some serial ∧
    ¬ Nonempty (PairIncrementOutcome serial)

/-- **Node `[180]`, periodic arm** (diagram tex 1213, "covered increment split:
periodic sparse-exit/Type B, or full-modulus arithmetic"): a routed periodic
alternative occurs for G's canonical serial system. -/
def PairIncrementEarlyOutcomeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ serial, canonicalPairSerialSystem data object = some serial ∧
    Nonempty (PairIncrementEarlyOutcome serial)

/-- Node `[180]`, arithmetic arm: no periodic routed alternative occurs for G's
canonical serial system (the literal negation at the same pinned system). -/
def PairIncrementNoEarlyOutcomeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ serial, canonicalPairSerialSystem data object = some serial ∧
    ¬ Nonempty (PairIncrementEarlyOutcome serial)

/-- **Node `[180]`, the arithmetic input**: G's canonical serial system carries
the full-modulus arithmetic data. -/
def PairSerialArithmeticStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ serial, canonicalPairSerialSystem data object = some serial ∧
    Nonempty (PairSerialArithmetic serial)

/-- The actual accepted cycle published by node `[180]` before the standard
incompatibility closure against node `[1]`. -/
def PairPowerOfTwoCycleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Graph.HasCycleWithLength data.LengthOK object

/-! ## Node `[182]` -/

/-- **Node `[182]`**: the one honest open endpoint for every exact place where
the paper's `[178]`--`[180]` chain is not exhaustive.  Each constructor retains
the canonical upstream object of G on which the corresponding claimed
implication fails. -/
inductive PairUncoveredResidual (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Type (u + 1) where
  | factorization (system : PairOverlapSystem data object)
      (selected : canonicalPairOverlapSystem data object = some system)
      (failure : ¬ system.ConditionalFactorization)
  | systemRealizability (returns : PairDemandReturns data object)
      (selected : canonicalPairDemandReturns data object = some returns)
      (failure : ¬ Nonempty (PairSystemRealizabilityOutcome returns))
  | incrementArithmetic (serial : PairSerialDemandSystem data object)
      (selected : canonicalPairSerialSystem data object = some serial)
      (failure : ¬ Nonempty (PairIncrementOutcome serial))

def PairConditionalFactorizationResidualStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  Nonempty (PairUncoveredResidual data object)

end Hypostructure.Graph.Strategy.Spine

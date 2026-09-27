import Hypostructure.Graph.Statements.SurplusPairCode

/-!
# Contract lemmas: the entropy counts of `[131]` and `[137]`

`prop:sparse-entropy-sandwich` and `prop:sparse-entropy-sandwich-with-blockers`
rest on one count: the mixed family of G's node-`[129]` spine family and G's
pair coordinates realizes its code among the labelled skeletons of G.  When
that count fails, the canonical realization of the spine family's code and the
failing pair set are what the pair-code chain `[178]` consumes.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[131]`, count fails: at G's node-`[129]` spine family and G's canonical
activation, blocker-free on the full schedule (node `[130]`), the failure of the
free-pair entropy count is the failure on the literal schedule, with the
canonical realization of the spine family's code. -/
theorem freePairCodeUnrealized_of_countFails
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (fails : FreePairCountFailsStatement data object)
    (baselineDemand : BaselineSpineDemandStatement data object)
    (independent : IndependentPairFamilyStatement data object) :
    FreePairCodeUnrealizedStatement data object := by
  classical
  obtain ⟨spine, spineSelected, spec⟩ := baselineDemand
  obtain ⟨activation, activationSelected, blockerFree⟩ := independent
  obtain ⟨realization, realizationSelected⟩ :=
    canonicalBaselineRealizationAt_spec object spine spec.2.1
  have scheduleCard : (codeSchedule data object).card =
      (object.degreeSurplus data.threshold).choose 2 :=
    object.card_portPairSchedule fun vertex =>
      le_trans atBaseline (object.minDegree_le_degree vertex)
  have countFailure :
      ¬ 2 ^ (spine.family.card + (codeSchedule data object).card) ≤
        Graph.skeletonBudget object := by
    intro count
    apply fails
    refine ⟨activation, spine, activationSelected, spineSelected, ?_⟩
    rwa [Graph.FiniteObject.DemandActivation.card_pairFamily]
  exact ⟨activation, spine, realization, activationSelected, spineSelected,
    realizationSelected, blockerFree, scheduleCard, countFailure,
    freeSide_nonempty_of_baseline_realized realization countFailure⟩

/-- Node `[137]`'s input: G's canonical capacity presentation (node `[136]`),
G's node-`[129]` spine family, and the schedule count of node `[134]`. -/
theorem blockedPairEntropySetup_of_ledgers
    (capacityLedger : CapacityTokenLedgerStatement data object)
    (pairLedger : CanonicalPairLedgerStatement data object)
    (baselineDemand : BaselineSpineDemandStatement data object) :
    BlockedPairEntropySetupStatement data object := by
  obtain ⟨capacity, capacitySelected, -⟩ := capacityLedger
  obtain ⟨_activation, _selected, _certificate, scheduleCard, -⟩ := pairLedger
  obtain ⟨spine, spineSelected, -⟩ := baselineDemand
  exact ⟨capacity, spine, capacitySelected, spineSelected, scheduleCard⟩

/-- Node `[137]`, free-side count fails: at G's canonical capacity presentation
and spine family, the failure of the free-side entropy count, with the
canonical realization of the spine family's code. -/
theorem blockedPairCodeUnrealized_of_countFails
    (fails : BlockedPairCountFailsStatement data object)
    (setup : BlockedPairEntropySetupStatement data object)
    (baselineDemand : BaselineSpineDemandStatement data object) :
    BlockedPairCodeUnrealizedStatement data object := by
  obtain ⟨capacity, spine, capacitySelected, spineSelected, scheduleCard⟩ := setup
  obtain ⟨spine', spineSelected', spec⟩ := baselineDemand
  obtain rfl : spine' = spine :=
    Option.some.inj (spineSelected'.symm.trans spineSelected)
  obtain ⟨realization, realizationSelected⟩ :=
    canonicalBaselineRealizationAt_spec object spine' spec.2.1
  have countFailure :
      ¬ 2 ^ (spine'.family.card + (codeFreeSide data object capacity).card) ≤
        Graph.skeletonBudget object := fun count =>
    fails ⟨capacity, capacitySelected, spine', spineSelected, count⟩
  exact ⟨capacity, spine', realization, capacitySelected, spineSelected,
    realizationSelected, scheduleCard, countFailure,
    freeSide_nonempty_of_baseline_realized realization countFailure⟩

end Hypostructure.Graph.Contracts.SurplusPair

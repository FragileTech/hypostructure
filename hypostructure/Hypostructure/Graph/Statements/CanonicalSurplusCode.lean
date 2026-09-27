import Hypostructure.Graph.Statements.SurplusPairOutcome
import Hypostructure.Graph.Statements.CanonicalTypeA

/-!
# Canonical objects of G: the pair-code chain `[131]`/`[137]`, `[178]`--`[180]`

The entropy counts of nodes `[131]` and `[137]` and the pair-code chain of
nodes `[178]`--`[180]` work with ONE baseline code realization of G's node-`[129]`
spine family, ONE pair set `Π` (the full schedule `Π(𝒜₀)` on the blocker-free
arm of `[130]`, the free side of G's capacity charge on the blocked arm,
`def:pair-overlap-system`, tex 5061-5066), its ONE first failed extension, and
the overlap system, minimal obstruction, demand returns, serial system and
routed outcomes built from them in turn.  Each is a witness an upstream
statement only asserts with `∃` (or `Nonempty`), so each is a canonical object
of G here, chosen at exactly the object fixed before it:

* `canonicalBaselineRealizationAt` -- a realization of the `[129]` family's code
  (the second conjunct of `BaselineSpineFamilySpec`);
* `canonicalCodePairSet` -- `Π`, selected by `[130]`'s own blocker predicate at
  G's canonical activation;
* `canonicalPairFirstFailure` -- the first failed extension packaged with its
  canonical response support (`PairOverlapFirstFailure.of`);
* `canonicalPairOverlapSystem` -- `def:pair-overlap-system` at that first
  failure, in the canonical encoding order of `Π`;
* `canonicalPairFailureOverlap` -- the minimal overlap obstruction of
  `lem:pair-failure-overlap` in that system;
* `canonicalPairDemandReturns` -- its two demands and canonical returns
  (`PairDemandReturns.of`);
* `canonicalRealizabilityOutcome`, `canonicalPairSerialSystem` -- the outcome of
  `lem:pair-system-realizability` for those returns, and its serial system;
* `canonicalIncrementOutcome` -- the outcome of
  `lem:pair-system-increment-arithmetic` for that serial system.

Every object is `Option`-valued; statements pin it with
`∃ x, obj = some x ∧ Q x`, which is false (never vacuously true) when it does
not exist.  This module imports no strategy, row or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

noncomputable section

variable (data : Parameters) (object : Graph.FiniteObject.{u})

/-! ## The baseline code realization and the pair set -/

/-- **The canonical realization of the `[129]` family's baseline code** at a
declared spine family. -/
def canonicalBaselineRealizationAt (spine : DeclaredCoordinateFamily object) :
    Option (Graph.BaselineCodeRealization object spine.family) :=
  canonicalChoice fun _ => True

theorem canonicalBaselineRealizationAt_spec (spine : DeclaredCoordinateFamily object)
    (exists_ : Nonempty (Graph.BaselineCodeRealization object spine.family)) :
    ∃ realization,
      canonicalBaselineRealizationAt object spine = some realization := by
  obtain ⟨realization⟩ := exists_
  obtain ⟨chosen, selected, -⟩ :=
    canonicalChoice_spec (spec := fun (_ : Graph.BaselineCodeRealization object
      spine.family) => True) ⟨realization, trivial⟩
  exact ⟨chosen, selected⟩

/-- The schedule `Π(𝒜₀)` of G. -/
abbrev codeSchedule : Finset (Finset (object.Vertex × object.Vertex)) :=
  object.portPairSchedule data.threshold

/-- The free side `Π_free` of a capacity presentation's charge. -/
abbrev codeFreeSide (capacity : SurplusCapacity data object) :
    Finset (Finset (object.Vertex × object.Vertex)) :=
  Graph.freeSide object.vertexPairDecidableEq (codeSchedule data object)
    capacity.tokenOrder capacity.Eligible capacity.eligibleDecidable

/-- **The canonical pair set `Π` of the pair code** (`def:pair-overlap-system`,
tex 5061-5066): at G's canonical activation, the full schedule when node
`[130]` finds no blocked pair (no pair has a blocker of any of the six clauses
of `def:surplus-blockers`), and otherwise the free side of G's canonical
capacity charge (node `[137]`). -/
def canonicalCodePairSet : Option (Finset (Finset (object.Vertex × object.Vertex))) := by
  classical
  exact match canonicalPairActivation data object with
    | none => none
    | some activation =>
        if Graph.HasSparsePairBlocker
            (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
            (LengthOK := data.LengthOK) activation (codeSchedule data object) then
          (canonicalCapacity data object).map (codeFreeSide data object)
        else some (codeSchedule data object)

theorem canonicalCodePairSet_eq_schedule
    {activation : object.DemandActivation object.PairCoordinate
      (object.Vertex × object.Vertex)}
    (selected : canonicalPairActivation data object = some activation)
    (free : ¬ Graph.HasSparsePairBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) activation (codeSchedule data object)) :
    canonicalCodePairSet data object = some (codeSchedule data object) := by
  classical
  unfold canonicalCodePairSet
  rw [selected]
  simp only [free, if_false]

theorem canonicalCodePairSet_eq_freeSide
    {activation : object.DemandActivation object.PairCoordinate
      (object.Vertex × object.Vertex)}
    {capacity : SurplusCapacity data object}
    (selected : canonicalPairActivation data object = some activation)
    (blocked : Graph.HasSparsePairBlocker
      (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
      (LengthOK := data.LengthOK) activation (codeSchedule data object))
    (capacitySelected : canonicalCapacity data object = some capacity) :
    canonicalCodePairSet data object = some (codeFreeSide data object capacity) := by
  classical
  unfold canonicalCodePairSet
  rw [selected]
  simp only [blocked, if_true, capacitySelected, Option.map_some]

/-! ## The first failed extension -/

/-- The conditions under which the pair code's first failure is packaged: the
active family, a nonempty pair set of free pairs of the schedule (no blocker
of any clause of `def:surplus-blockers`), the count failure at the realized baseline family,
and connectedness (node `[8]`). -/
def PairFirstFailureConditions (spine : DeclaredCoordinateFamily object)
    (pairSet : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  ∃ active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold,
    pairSet.Nonempty ∧
    pairSet ⊆ codeSchedule data object ∧
    (∀ pair, pair ∈ pairSet →
      ¬ ((Graph.recordSparsePairDEBlockers
          (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
          (LengthOK := data.LengthOK) (Graph.pairResponseActivation active)
          (codeSchedule data object)).blockers pair).Nonempty) ∧
    ¬ 2 ^ (spine.family.card + pairSet.card) ≤ Graph.skeletonBudget object ∧
    object.graph.Connected

/-- The first-failure package at a spine family, realization and pair set. -/
def pairFirstFailureOf (spine : DeclaredCoordinateFamily object)
    (realization : Graph.BaselineCodeRealization object spine.family)
    (pairSet : Finset (Finset (object.Vertex × object.Vertex)))
    (conditions : PairFirstFailureConditions data object spine pairSet) :
    PairOverlapFirstFailure data object :=
  PairOverlapFirstFailure.of data object conditions.choose spine.Coordinate
    spine.family spine.coordinateSupport realization pairSet
    conditions.choose_spec.1 conditions.choose_spec.2.1
    conditions.choose_spec.2.2.1
    (firstFailedPairExtensionOf realization conditions.choose_spec.2.2.2.1)
    conditions.choose_spec.2.2.2.2

/-- **The canonical first failed pair extension of G's pair code**
(`def:pair-overlap-system`, tex 5061-5068): the least failed extension
(`firstFailedPairExtensionOf`) of the canonical realization of the `[129]`
family's code by the canonical pair set, with the failed pair's canonical
response support `X_π`. -/
def canonicalPairFirstFailure : Option (PairOverlapFirstFailure data object) := by
  classical
  exact match canonicalBaselineSpineFamily data object with
    | none => none
    | some spine =>
        match canonicalBaselineRealizationAt object spine,
            canonicalCodePairSet data object with
        | some realization, some pairSet =>
            if conditions : PairFirstFailureConditions data object spine pairSet then
              some (pairFirstFailureOf data object spine realization pairSet
                conditions)
            else none
        | _, _ => none

theorem canonicalPairFirstFailure_isSome
    {spine : DeclaredCoordinateFamily object}
    {realization : Graph.BaselineCodeRealization object spine.family}
    {pairSet : Finset (Finset (object.Vertex × object.Vertex))}
    (spineSelected : canonicalBaselineSpineFamily data object = some spine)
    (realizationSelected :
      canonicalBaselineRealizationAt object spine = some realization)
    (pairSetSelected : canonicalCodePairSet data object = some pairSet)
    (conditions : PairFirstFailureConditions data object spine pairSet) :
    ∃ first, canonicalPairFirstFailure data object = some first := by
  classical
  refine ⟨pairFirstFailureOf data object spine realization pairSet conditions, ?_⟩
  unfold canonicalPairFirstFailure
  rw [spineSelected]
  simp only
  rw [realizationSelected, pairSetSelected]
  simp only [dif_pos conditions]

/-! ## The overlap system and the minimal obstruction -/

/-- **Spec of the overlap system** of `def:pair-overlap-system` at a first
failure: it is built on exactly that first failure, and its coordinates are
ranked in the canonical encoding order of `Π`. -/
def PairOverlapSystemSpec (first : PairOverlapFirstFailure data object)
    (system : PairOverlapSystem data object) : Prop := by
  classical
  exact system.first = first ∧
    ∀ pair, system.rank pair = system.first.pairSet.toList.idxOf pair.1

/-- **The canonical pair-overlap system of G** (node `[178]`). -/
def canonicalPairOverlapSystem : Option (PairOverlapSystem data object) :=
  (canonicalPairFirstFailure data object).bind fun first =>
    canonicalChoice (PairOverlapSystemSpec data object first)

/-- **The canonical minimal overlap obstruction of G** (`lem:pair-failure-overlap`,
node `[178]`) in the canonical overlap system. -/
def canonicalPairFailureOverlap : Option (PairFailureOverlap data object) :=
  (canonicalPairOverlapSystem data object).bind fun system =>
    canonicalChoice fun overlap : PairFailureOverlap data object =>
      overlap.system = system

/-- **The canonical demand returns of G** (node `[179]`): the two demands of the
canonical obstruction's failed pair with their canonical returns. -/
def canonicalPairDemandReturns : Option (PairDemandReturns data object) :=
  (canonicalPairFailureOverlap data object).map PairDemandReturns.of

/-! ## The routed outcomes of nodes `[179]` and `[180]` -/

/-- **The canonical outcome of `lem:pair-system-realizability`** for a retained
return system. -/
def canonicalRealizabilityOutcome (returns : PairDemandReturns data object) :
    Option (PairSystemRealizabilityOutcome returns) :=
  canonicalChoice fun _ => True

theorem canonicalRealizabilityOutcome_spec (returns : PairDemandReturns data object)
    (covered : Nonempty (PairSystemRealizabilityOutcome returns)) :
    ∃ outcome, canonicalRealizabilityOutcome data object returns = some outcome := by
  obtain ⟨outcome⟩ := covered
  obtain ⟨chosen, selected, -⟩ :=
    canonicalChoice_spec (spec := fun (_ : PairSystemRealizabilityOutcome returns) =>
      True) ⟨outcome, trivial⟩
  exact ⟨chosen, selected⟩

/-- **The canonical serial demand system of G** (node `[179]`, alternative (v)):
the serial system of the canonical outcome of the canonical returns, when that
outcome is serial. -/
def canonicalPairSerialSystem : Option (PairSerialDemandSystem data object) :=
  (canonicalPairDemandReturns data object).bind fun returns =>
    match canonicalRealizabilityOutcome data object returns with
    | some (.serial system _) => some system
    | _ => none

/-- **The canonical outcome of `lem:pair-system-increment-arithmetic`** for a
serial demand system (node `[180]`). -/
def canonicalIncrementOutcome (serial : PairSerialDemandSystem data object) :
    Option (PairIncrementOutcome serial) :=
  canonicalChoice fun _ => True

theorem canonicalIncrementOutcome_spec (serial : PairSerialDemandSystem data object)
    (covered : Nonempty (PairIncrementOutcome serial)) :
    ∃ outcome, canonicalIncrementOutcome data object serial = some outcome := by
  obtain ⟨outcome⟩ := covered
  obtain ⟨chosen, selected, -⟩ :=
    canonicalChoice_spec (spec := fun (_ : PairIncrementOutcome serial) => True)
      ⟨outcome, trivial⟩
  exact ⟨chosen, selected⟩

end

end Hypostructure.Graph.Strategy.Spine

import Hypostructure.Graph.Statements.Spine

/-!
# Canonical objects: the cold branch

Proof-agnostic canonical objects of the selected residual `G` on the surviving
cold branch (`lem:cold-germ-extraction` tex ~7297, `def:neutral-equal-length-germ`
tex ~7700, `lem:neutral-germ-symmetry` tex ~7715, `lem:two-strand-check`
tex ~7759, `lem:refined-minimality-swap` tex ~7732).  This module imports no
strategy, row or vocabulary module.

## Design (shared by every `Statements/Canonical*` module)

A fact value is data-free (`FactSystem.value_subsingleton`), so an object that
an upstream key only asserts with `∃` is named downstream as a canonical
function of `G`: `Classical.choose` of *that upstream statement's* `∃`-body at
`G`.  A guarded object is `Option`-valued,

  `if h : ∃ x, Spec data G x then some (Classical.choose h) else none`,

with `_spec`, `_spec_of_eq_some` and `_eq_none_iff`.  A downstream statement
pins it as `∃ x, obj data G = some x ∧ Q x`: false, never vacuous, when the
upstream existence fails.

## The objects

* `coldGermExtraction?` — node `[153]`/`[219]`'s disjoint germ family together
  with its corridor loss: `Classical.choose` of the `∃ disjointFamily
  corridorLoss` of `ColdGermCandidatesStatement`, whose incidence and candidate
  set are already pinned by equations to the routed ones
  (`coldRoutedOccurrenceIncidence`, `coldRoutedCandidates`).  The pre-refactor
  consumers (d2ded0e `ColdCorridorRows/GermFamilyPositive.lean`,
  `GermTrichotomy.lean`, `AbsorbedGerm.lean`) `rcases`ed exactly this `∃` of
  `K .coldGermCandidates`; its extraction is the greedy
  `coldGermOccurrenceExtractionLocal` (`exists_independent_card_le_mul`).
  `coldGermDisjointFamily?` and `coldGermCorridorLoss?` are its projections.
* `CanonicalActiveColdGerm` — membership in that one family: the only
  remaining `∃` is over the occurrence index inside the fixed family.
* `markedNeutralGerm?` — node `[406]`'s marked neutral equal-length germ and its
  marked canonical exchange representative: `Classical.choose` of the
  `∃ germ representative` of `NeutralEqualLengthTerminalConfigurationStatement`.
  The pre-refactor decision `neutralGermSymmetryDichotomy` (d2ded0e
  `ColdCorridorRows/NeutralTerminal.lean`) set `germ := Classical.choose
  neutral.2` and `representative := Classical.choose (Classical.choose_spec
  neutral.2)` for exactly this fact; nodes `[233]`, `[234]`, `[410]`, `[244]`,
  `[245]`, `[408]`, `[409]` concern this configuration.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-! ## The extracted disjoint germ family of node `[153]` -/

/-- The `∃ disjointFamily corridorLoss`-body of `ColdGermCandidatesStatement`
(node `[219]`, `lem:cold-germ-extraction`), with the incidence and candidate
set at their pinned routed values. -/
noncomputable def ColdGermExtractionSpec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (extraction : Finset (ColdGermOccurrence data object) × Nat) : Prop :=
  ∃ routing : ColdFailureRoutingStatement data object,
    ColdGermFamilyWitness data object routing
      (coldRoutedOccurrenceIncidence data object routing)
      (coldRoutedCandidates data object routing) extraction.1 extraction.2

/-- Node `[219]` is literally the existence of its extraction at the routed
incidence and candidates. -/
theorem coldGermCandidates_iff_exists_extractionSpec (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    ColdGermCandidatesStatement data object ↔
      ∃ extraction, ColdGermExtractionSpec data object extraction := by
  classical
  constructor
  · intro candidates
    unfold ColdGermCandidatesStatement at candidates
    obtain ⟨routing, incidence, candidates, disjointFamily, corridorLoss,
      witness⟩ := candidates
    have witness' := witness
    simp only [ColdGermFamilyWitness] at witness'
    obtain ⟨incidenceEq, candidatesEq, -⟩ := witness'
    subst incidenceEq
    subst candidatesEq
    exact ⟨(disjointFamily, corridorLoss), routing, witness⟩
  · rintro ⟨extraction, routing, witness⟩
    unfold ColdGermCandidatesStatement
    exact ⟨routing, _, _, extraction.1, extraction.2, witness⟩

/-- **The canonical extraction of node `[153]`**: `Classical.choose` of node
`[219]`'s disjoint family and corridor loss. -/
noncomputable def coldGermExtraction? (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Finset (ColdGermOccurrence data object) × Nat) := by
  classical
  exact if h : ∃ extraction, ColdGermExtractionSpec data object extraction then
    some (Classical.choose h) else none

theorem coldGermExtraction?_spec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (h : ∃ extraction, ColdGermExtractionSpec data object extraction) :
    ∃ extraction, coldGermExtraction? data object = some extraction ∧
      ColdGermExtractionSpec data object extraction := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [coldGermExtraction?, h]

theorem coldGermExtraction?_spec_of_eq_some (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {extraction : Finset (ColdGermOccurrence data object) × Nat}
    (eq : coldGermExtraction? data object = some extraction) :
    ColdGermExtractionSpec data object extraction := by
  classical
  unfold coldGermExtraction? at eq
  split at eq
  · next h =>
      cases eq
      exact Classical.choose_spec h
  · cases eq

theorem coldGermExtraction?_eq_none_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    coldGermExtraction? data object = none ↔
      ¬ ∃ extraction, ColdGermExtractionSpec data object extraction := by
  classical
  unfold coldGermExtraction?
  split <;> simp_all

/-- On node `[219]`'s ledger the canonical extraction exists. -/
theorem coldGermExtraction?_spec_of_candidates (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (candidates : ColdGermCandidatesStatement data object) :
    ∃ extraction, coldGermExtraction? data object = some extraction ∧
      ColdGermExtractionSpec data object extraction :=
  coldGermExtraction?_spec data object
    ((coldGermCandidates_iff_exists_extractionSpec data object).1 candidates)

/-- The canonical greedy disjoint germ family (the first projection). -/
noncomputable def coldGermDisjointFamily? (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Finset (ColdGermOccurrence data object)) :=
  (coldGermExtraction? data object).map Prod.fst

/-- Its canonical corridor loss (the second projection). -/
noncomputable def coldGermCorridorLoss? (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option Nat :=
  (coldGermExtraction? data object).map Prod.snd

/-- **A germ of the canonical extracted family**: the incidence of some
occurrence of the one fixed family `coldGermDisjointFamily?`.  The routing
fact is a proposition, so the routed incidence does not depend on its proof. -/
noncomputable def CanonicalActiveColdGerm (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object) : Prop :=
  ∃ extraction, coldGermExtraction? data object = some extraction ∧
    ∃ routing : ColdFailureRoutingStatement data object,
      ∃ occurrence ∈ extraction.1,
        coldRoutedOccurrenceIncidence data object routing occurrence = germ

/-! ## The marked neutral equal-length germ of node `[406]` -/

/-- A germ together with a canonical exchange representative at its
interface: the pair node `[406]` marks. -/
abbrev MarkedNeutralGermData (data : Parameters)
    (object : Graph.FiniteObject.{u}) :=
  Σ germ : Graph.ColdCorridor.BoundedGerm data.coldSignature
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object,
    Graph.CanonicalPiece germ.atom.interface

/-- The `∃ germ representative`-body of node `[406]`
(`NeutralEqualLengthTerminalConfigurationStatement`,
`def:neutral-equal-length-germ`, tex ~7700). -/
noncomputable def MarkedNeutralGermSpec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (marked : MarkedNeutralGermData data object) : Prop :=
  NeutralEqualLengthTerminalConfigurationAt data object marked.1 marked.2

theorem neutralEqualLengthTerminal_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    NeutralEqualLengthTerminalConfigurationStatement data object ↔
      DenseColdCorridorsTerminalStatement data object ∧
        ∃ marked, MarkedNeutralGermSpec data object marked := by
  constructor
  · rintro ⟨terminal, germ, representative, at_⟩
    exact ⟨terminal, ⟨germ, representative⟩, at_⟩
  · rintro ⟨terminal, ⟨germ, representative⟩, at_⟩
    exact ⟨terminal, germ, representative, at_⟩

/-- **The marked neutral germ**: `Classical.choose` of node `[406]`'s
`∃ germ representative`. -/
noncomputable def markedNeutralGerm? (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (MarkedNeutralGermData data object) := by
  classical
  exact if h : ∃ marked, MarkedNeutralGermSpec data object marked then
    some (Classical.choose h) else none

theorem markedNeutralGerm?_spec (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (h : ∃ marked, MarkedNeutralGermSpec data object marked) :
    ∃ marked, markedNeutralGerm? data object = some marked ∧
      MarkedNeutralGermSpec data object marked := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [markedNeutralGerm?, h]

theorem markedNeutralGerm?_spec_of_eq_some (data : Parameters)
    (object : Graph.FiniteObject.{u})
    {marked : MarkedNeutralGermData data object}
    (eq : markedNeutralGerm? data object = some marked) :
    MarkedNeutralGermSpec data object marked := by
  classical
  unfold markedNeutralGerm? at eq
  split at eq
  · next h =>
      cases eq
      exact Classical.choose_spec h
  · cases eq

theorem markedNeutralGerm?_eq_none_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    markedNeutralGerm? data object = none ↔
      ¬ ∃ marked, MarkedNeutralGermSpec data object marked := by
  classical
  unfold markedNeutralGerm?
  split <;> simp_all

/-- On node `[406]`'s ledger the marked germ exists. -/
theorem markedNeutralGerm?_spec_of_terminal (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (neutral : NeutralEqualLengthTerminalConfigurationStatement data object) :
    ∃ marked, markedNeutralGerm? data object = some marked ∧
      MarkedNeutralGermSpec data object marked :=
  markedNeutralGerm?_spec data object
    ((neutralEqualLengthTerminal_iff data object).1 neutral).2

end Hypostructure.Graph.Strategy.Spine

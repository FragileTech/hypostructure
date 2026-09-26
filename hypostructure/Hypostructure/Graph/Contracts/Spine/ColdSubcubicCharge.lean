import Hypostructure.Graph.Statements.Spine

/-!
# Contract: the full charge of a subcubic cold half-edge (`[153]`, `[175]`)

`lem:absorbed-germ-fan-data` (i), tex 7920-7922: *"`J` contains no vertex of
degree at least `4`.  Then `J` is subcubic, the count of
`lem:cold-germ-extraction` charges `ε` in full"* -- together with
`lem:cold-germ-extraction` (tex 7318-7322: after deleting the already routed
handoff incidences, *"each remaining selected half-edge supplies one canonical
first-failure cold bounded configuration"*).  On the routed cold residual the
first failure of every selected half-edge is (F5) or (F4)
(`ColdSurvivingFirstFailureStatement`); the paper's claim is that a half-edge
whose bounded first-failure prefix is subcubic is charged in full as an (F5)
candidate, i.e. it is not an (F4) handoff of the declared registry.

This is recorded as a paper error (`lean-vs-paper-discrepancies.md#paper-errors`):
with the registry the paper declares at (F4) (declared Type B envelope cores and
route-8 response supports), a corridor can first enter a declared support at a
subcubic vertex -- its foot already lies in the support
(`Quarantine/PaperRepairs/ColdF4Charge.lean`, `coldF4_of_foot_declared`) -- and
nothing in the paper bounds or excludes those half-edges.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

/-- **`lem:absorbed-germ-fan-data` (i), the paper's claim**: a selected
half-edge whose bounded first-failure prefix is subcubic is an (F5)
configuration of the routed classification, not an (F4) handoff. -/
theorem coldSubcubicFirstFailureGerm (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (routing : ColdFailureRoutingStatement data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (subcubic : ∀ vertex ∈
        (coldOccurrenceCorridorAt data object
          (coldRoutedClassified data object routing) epsilon).prefixSupport
          (coldRoutedTraceEnd data object routing epsilon),
        object.degree vertex ≤ data.threshold) :
    ColdFirstFailureGermOccurrence data object
      (coldRoutedClassified data object routing) epsilon := by
  rcases Classical.choose_spec routing.surviving.holds epsilon with germ | handoff
  · exact germ
  · -- PAPER-ERROR [153] tex:7920 — see lean-vs-paper-discrepancies.md#paper-errors
    sorry

end Hypostructure.Graph.Contracts.Spine

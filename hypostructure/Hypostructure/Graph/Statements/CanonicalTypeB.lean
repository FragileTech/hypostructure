import Hypostructure.Graph.Statements.CanonicalTypeA
import Hypostructure.Graph.Statements.TypeB

/-!
# Canonical objects of the selected counterexample: Type B

Node `[65]` receives **one** assigned Type B support `X = (Y_X, H_X)` of the
selected counterexample `G`, in one of the manuscript's entry forms, each tied
to the upstream object that produced it:

* ordinary (`[62]` yes → `[64]`, `def:typeB-assigned-ledger`, tex 961): `Y_X`
  is the negative support `X₀` of node `[61]` and `H_X` its high centres;
* decorated (`[108]`, `def:decorated-fan-envelope`, tex 10898): `Y_X = X₀` and
  `H_X = {z}` for the canonical surviving exit-`(7)` separator `z` of `X₀`
  (`canonicalHandoffSeparatorAt`), with the envelope `envelopeOfSeparation`;
* absorbed (`[177]`, `lem:absorbed-germ-fan-data` (ii), tex 7915): for each
  selected half-edge `ε`, `Y_X` is the support of `ε`'s routed germ and `H_X`
  its first high centre, chosen from node `[177]`'s own `∃ centre`;
* same-token (`[144]`): see the note at the end of this file.

Also named here, once: the Type B fan-window profile at a centre over the
fixed packed-window union `W₀ = windowSupport P₀`, and the B2 disjoint ledger
of a support at `P₀`.

The design is the one of `CanonicalTypeA`: every guarded object is
`canonicalChoice` of the literal `∃`-body of its upstream key (`Option`
valued; downstream pins read `∃ x, obj = some x ∧ Q x`, which is false, never
vacuous, when the object is absent).
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-! ## Ordinary and decorated supports -/

/-- **The ordinary Type B support** `(X₀, H(X₀))` of node `[64]`: the node-`[61]`
negative support and its high centres (`TypeBRefinedSupport.centres`,
`def:canonical-decomp`).  d2ded0e: `[68]` destructured `K .typeBFanEntry`'s
ordinary lane, itself produced from `K .typeBHighSurplus`, i.e. the split of
node `[62]` at the `K .negativeSupport` component. -/
noncomputable def canonicalTypeBOrdinarySupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Finset object.Vertex × Finset object.Vertex) :=
  (canonicalNegativePiece data object).map fun core =>
    (core, Graph.TypeBRefinedSupport.centres object data.threshold core)

/-- **The decorated Type B support** `(X₀, {z})` of node `[108]`: `z` is the
canonical surviving exit-`(7)` separator of `X₀` (`lem:typeA-high-degree-handoff`,
tex 11110: "take `Y = X` ... and `H = {z}`").  d2ded0e: the decorated lane read
`K .typeAExitSevenHandoff`'s envelope. -/
noncomputable def canonicalTypeBDecoratedSupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Finset object.Vertex × Finset object.Vertex) :=
  (canonicalNegativePiece data object).bind fun core =>
    (canonicalHandoffSeparatorAt data object core).map fun separator =>
      (core, {separator})

/-- The decorated envelope of node `[108]`: the canonical exit-`(7)` envelope of
`X₀`, at the registered high-degree set and the exit-`(3)` absorbing clause of
the fixed packing `P₀`. -/
noncomputable def canonicalTypeBDecoratedEnvelope (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object)
      (handoffAbsorbing data object (canonicalWindowPacking data object))) :=
  (canonicalNegativePiece data object).bind fun core =>
    canonicalHandoffEnvelopeAt data object core (handoffHighDegree data object)
      (handoffAbsorbing data object (canonicalWindowPacking data object))

theorem canonicalTypeBDecoratedEnvelope_core {data : Parameters}
    {object : Graph.FiniteObject.{u}} {envelope}
    (h : canonicalTypeBDecoratedEnvelope data object = some envelope) :
    ∃ core, canonicalNegativePiece data object = some core ∧ envelope.core = core := by
  obtain ⟨core, coreEq, envelopeEq⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨core, coreEq, canonicalHandoffEnvelopeAt_core envelopeEq⟩

/-! ## Absorbed supports of node `[177]` -/

/-- The first-high centre of one selected half-edge's absorbed germ: the
`∃ centre` of node `[177]` (`AbsorbedGermDecoratedAssignedSupportStatement`,
`lem:absorbed-germ-fan-data` (ii)) at `ε`, read at the node-`[153]` routing
(`K .coldFailureRouting`, a proposition, so its classified data is canonical). -/
noncomputable def canonicalAbsorbedCentre (data : Parameters)
    (object : Graph.FiniteObject.{u}) (epsilon : ColdEligibleHalfEdge data object) :
    Option object.Vertex := by
  classical
  exact if routing : ColdFailureRoutingStatement data object then
    canonicalChoice (AbsorbedGermFanEnvelopeWitness data object
      (coldOccurrenceIncidence data object
        (coldRoutedClassified data object routing) epsilon))
  else none

theorem canonicalAbsorbedCentre_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {epsilon : ColdEligibleHalfEdge data object}
    (routing : ColdFailureRoutingStatement data object)
    (h : ∃ centre, AbsorbedGermFanEnvelopeWitness data object
      (coldOccurrenceIncidence data object
        (coldRoutedClassified data object routing) epsilon) centre) :
    ∃ centre, canonicalAbsorbedCentre data object epsilon = some centre ∧
      AbsorbedGermFanEnvelopeWitness data object
        (coldOccurrenceIncidence data object
          (coldRoutedClassified data object routing) epsilon) centre := by
  classical
  simpa [canonicalAbsorbedCentre, routing] using canonicalChoice_spec h

theorem canonicalAbsorbedCentre_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {epsilon : ColdEligibleHalfEdge data object}
    {centre : object.Vertex}
    (h : canonicalAbsorbedCentre data object epsilon = some centre) :
    ∃ routing : ColdFailureRoutingStatement data object,
      AbsorbedGermFanEnvelopeWitness data object
        (coldOccurrenceIncidence data object
          (coldRoutedClassified data object routing) epsilon) centre := by
  classical
  unfold canonicalAbsorbedCentre at h
  split at h
  · next routing => exact ⟨routing, canonicalChoice_spec_of_eq_some h⟩
  · cases h

theorem canonicalAbsorbedCentre_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {epsilon : ColdEligibleHalfEdge data object} :
    canonicalAbsorbedCentre data object epsilon = none ↔
      ∀ routing : ColdFailureRoutingStatement data object,
        ¬ ∃ centre, AbsorbedGermFanEnvelopeWitness data object
          (coldOccurrenceIncidence data object
            (coldRoutedClassified data object routing) epsilon) centre := by
  classical
  unfold canonicalAbsorbedCentre
  split
  · next routing =>
      rw [canonicalChoice_eq_none_iff]
      exact ⟨fun h _ => h, fun h => h routing⟩
  · next noRouting =>
      exact ⟨fun _ routing => absurd routing noRouting, fun _ => rfl⟩

/-- **The absorbed Type B support of `ε`** `(V(germ ε), {first high centre})`
(`TypeBAbsorbedForm`: `core = germ.support`, `centres = {centre}`). -/
noncomputable def canonicalTypeBAbsorbedSupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) (epsilon : ColdEligibleHalfEdge data object) :
    Option (Finset object.Vertex × Finset object.Vertex) := by
  classical
  exact if routing : ColdFailureRoutingStatement data object then
    (canonicalAbsorbedCentre data object epsilon).map fun centre =>
      ((coldOccurrenceIncidence data object
        (coldRoutedClassified data object routing) epsilon).support, {centre})
  else none

/-! ## The Type B fan-window profile at `W₀` -/

/-- **The canonical Type B profile** at a centre of the fan degree window, over
the packed-window union `W₀ = windowSupport P₀` of the fixed maximal packing
(`def:fan-closed-port`, tex 13158; `lem:typeB-hybrid-B1`, tex 13125). -/
noncomputable def canonicalTypeBProfile (data : Parameters)
    (object : Graph.FiniteObject.{u}) (centre : object.Vertex) :
    Option (Graph.TypeBFanClosedPorts.Profile object) := by
  classical
  exact if degrees : 4 ≤ object.degree centre ∧ object.degree centre ≤ 8 then
    some (Graph.TypeBProfileSchedule.canonicalProfile object
      (Graph.FiniteObject.windowSupport (canonicalWindowPacking data object))
      centre degrees.1 degrees.2)
  else none

/-! ## The B2 disjoint ledger -/

/-- The existence premise of the B2 ledger of a support at `P₀`: the disjoint
choice of the B2 yes arm (`K .typeBB2Choice`, `def:typeB-bridge-statements`
B2, tex 14119) at the assigned centres, which are high and include the core's
high centres (`DisjointLedger`'s two propositional fields). -/
def TypeBLedgerSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex) : Prop :=
  Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres centres ∧
    (∀ hub ∈ centres, Graph.IsHighCentre object data.threshold hub) ∧
    Graph.TypeBRefinedSupport.centres object data.threshold core ⊆ centres

/-- **The B2 disjoint ledger of `(Y, H)`**: the `Classical.choice` of the B2
disjoint choice, exactly as `Contracts.TypeB.typeBDisjointLedger` builds it
(`⟨Classical.choice (choice …), high, subset⟩`), now one named object so that
`[74]`, `[76]` and `[85]` all speak about the same ledger. -/
noncomputable def canonicalTypeBDisjointChoice (data : Parameters)
    (object : Graph.FiniteObject.{u}) (core centres : Finset object.Vertex) :
    Option (Graph.TypeBRefinedSupport.DisjointLedger object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres) := by
  classical
  exact if h : TypeBLedgerSpec data object core centres then
    some ⟨Classical.choice h.1, h.2.1, h.2.2⟩
  else none

theorem canonicalTypeBDisjointChoice_isSome_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {core centres : Finset object.Vertex} :
    (canonicalTypeBDisjointChoice data object core centres).isSome ↔
      TypeBLedgerSpec data object core centres := by
  classical
  unfold canonicalTypeBDisjointChoice
  split
  · next h => simp [h]
  · next h => simp [h]

/-! ## Note: the same-token support of node `[144]`

`SameTokenTypeBHandoffStatement` (Statements/SurplusPair.lean) buries its
envelope `envelopeOfFirstSeparator {dp.2, dq.2} h …` (core `{dp.2, dq.2}`,
decorations `{h}`) under the whole `∃ active ∃ capacity … ∃ pattern` chain, so
its support is not an `∃`-body over `(Y, H)` and cannot be `Classical.choose`d
without restating the key.  It is deliberately not defined here: once node
`[144]` is restated as `∃ core centres, SameTokenHandoffAt data G core centres`,
the object is `canonicalChoice (fun support =>
SameTokenHandoffAt data G support.1 support.2)` in a module after
`Statements/SurplusPair.lean`. -/

end Hypostructure.Graph.Strategy.Spine

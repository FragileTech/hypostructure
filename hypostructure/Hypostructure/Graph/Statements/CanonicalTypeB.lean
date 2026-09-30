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
* absorbed (`[177]`, `lem:absorbed-germ-fan-data` (ii), tex 7915): at the
  canonical selected half-edge `ε` outside the subcubic candidates, `Y_X` is
  `ε`'s retained first-failure prefix (the counted core of the `[177]`
  envelope) and `H_X` its first high centre, chosen from node `[177]`'s own
  `∃ centre` at `ε`;
* same-token (`[144]`): see the note at the end of this file.

Also named here, once: the B2 disjoint ledger of a support at `P₀`.

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

/-! ## The absorbed support of node `[177]` -/

/-- The absorbed handoff `(z, Y)` of one selected half-edge `ε`: the canonical
choice of node `[177]`'s `∃ handoff` at `ε` itself (`AbsorbedHandoffAt`,
`lem:absorbed-germ-fan-data` (ii)), read at the node-`[153]` routing
(`K .coldFailureRouting`, a proposition, so its classified data is
canonical). -/
noncomputable def canonicalAbsorbedHandoff (data : Parameters)
    (object : Graph.FiniteObject.{u}) (epsilon : ColdEligibleHalfEdge data object) :
    Option (object.Vertex × Finset object.Vertex) := by
  classical
  exact if routing : ColdFailureRoutingStatement data object then
    canonicalChoice (AbsorbedHandoffAt data object routing epsilon)
  else none

theorem canonicalAbsorbedHandoff_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {epsilon : ColdEligibleHalfEdge data object}
    (routing : ColdFailureRoutingStatement data object)
    (h : ∃ handoff, AbsorbedHandoffAt data object routing epsilon handoff) :
    ∃ handoff, canonicalAbsorbedHandoff data object epsilon = some handoff ∧
      AbsorbedHandoffAt data object routing epsilon handoff := by
  classical
  simpa [canonicalAbsorbedHandoff, routing] using canonicalChoice_spec h

theorem canonicalAbsorbedHandoff_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {epsilon : ColdEligibleHalfEdge data object}
    {handoff : object.Vertex × Finset object.Vertex}
    (h : canonicalAbsorbedHandoff data object epsilon = some handoff) :
    ∃ routing : ColdFailureRoutingStatement data object,
      AbsorbedHandoffAt data object routing epsilon handoff := by
  classical
  unfold canonicalAbsorbedHandoff at h
  split at h
  · next routing => exact ⟨routing, canonicalChoice_spec_of_eq_some h⟩
  · cases h

/-- **A selected half-edge whose corridor meets a high-degree vertex**
(`lem:absorbed-germ-fan-data` (ii), the yes arm of node `[175]`): it lies
outside node `[153]`'s routed subcubic candidate set. -/
def AbsorbedHalfEdgeOutside (data : Parameters) (object : Graph.FiniteObject.{u})
    (epsilon : ColdEligibleHalfEdge data object) : Prop :=
  ∃ routing : ColdFailureRoutingStatement data object,
    Sum.inl epsilon ∉ coldRoutedCandidates data object routing

/-- **The absorbed half-edge of `G`**: the canonical choice of a selected
half-edge outside the subcubic candidates (`none` when every selected corridor
is subcubic). -/
noncomputable def canonicalTypeBAbsorbedHalfEdge (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option (ColdEligibleHalfEdge data object) :=
  canonicalChoice (AbsorbedHalfEdgeOutside data object)

/-- **`H_X` of the absorbed Type B support** with handoff `(z, Y)`: the
high-degree fan centres whose surplus units are assigned to it
(`def:typeB-assigned-ledger`, tex 12909, with `def:canonical-decomp`, tex 10063):
the envelope's decoration `z` together with the high vertices of `Y` (all
surplus units of a high vertex of `R` go to the support containing it).  The
envelope's own decorations stay `{z}`; `H_X` is the Type B fan-centre set of the
support. -/
noncomputable def absorbedAssignedCentres (data : Parameters)
    (object : Graph.FiniteObject.{u}) (centre : object.Vertex)
    (core : Finset object.Vertex) : Finset object.Vertex := by
  classical
  exact insert centre (Graph.TypeBRefinedSupport.centres object data.threshold core)

theorem mem_absorbedAssignedCentres {data : Parameters}
    {object : Graph.FiniteObject.{u}} {centre vertex : object.Vertex}
    {core : Finset object.Vertex} :
    vertex ∈ absorbedAssignedCentres data object centre core ↔
      vertex = centre ∨
        vertex ∈ Graph.TypeBRefinedSupport.centres object data.threshold core := by
  classical
  unfold absorbedAssignedCentres
  exact Finset.mem_insert

theorem centre_mem_absorbedAssignedCentres {data : Parameters}
    {object : Graph.FiniteObject.{u}} {centre : object.Vertex}
    {core : Finset object.Vertex} :
    centre ∈ absorbedAssignedCentres data object centre core :=
  mem_absorbedAssignedCentres.2 (Or.inl rfl)

theorem centres_subset_absorbedAssignedCentres {data : Parameters}
    {object : Graph.FiniteObject.{u}} {centre : object.Vertex}
    {core : Finset object.Vertex} :
    Graph.TypeBRefinedSupport.centres object data.threshold core ⊆
      absorbedAssignedCentres data object centre core :=
  fun _ member => mem_absorbedAssignedCentres.2 (Or.inr member)

/-- The absorbed Type B support `(Y_X, H_X)` at one selected half-edge `ε`: the
counted core `Y` of node `[177]`'s envelope `(Y, {z})`, and
`H_X = absorbedAssignedCentres z Y = {z} ∪ centres(Y)`. -/
noncomputable def canonicalTypeBAbsorbedSupportAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (epsilon : ColdEligibleHalfEdge data object) :
    Option (Finset object.Vertex × Finset object.Vertex) :=
  (canonicalAbsorbedHandoff data object epsilon).map fun handoff =>
    (handoff.2, absorbedAssignedCentres data object handoff.1 handoff.2)

/-- **The absorbed Type B support of `G`** (node `[177]` → `[65]`): the support
`(Y_X, H_X)` of the canonical absorbed half-edge. -/
noncomputable def canonicalTypeBAbsorbedSupport (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Finset object.Vertex × Finset object.Vertex) :=
  (canonicalTypeBAbsorbedHalfEdge data object).bind
    (canonicalTypeBAbsorbedSupportAt data object)

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
(`⟨Classical.choice (choice …), high, subset⟩`), as one named object so that
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

The same-token support is `canonicalSameTokenSupport`
(`Statements/CanonicalSameToken.lean`): the canonical choice of the
`∃ core centres, SameTokenHandoffAt data G core centres` body of node `[144]`.
It is defined after `Statements/SurplusPair.lean`, which this module does not
import. -/

end Hypostructure.Graph.Strategy.Spine

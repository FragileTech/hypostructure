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

/-- The case-(ii) handoff of one selected half-edge `ε`: the canonical choice of
node `[177]`'s `∃ centre core` at `ε` itself (`AbsorbedHandoffAt`,
`lem:absorbed-germ-fan-data` (ii)) --- the first high centre `z` of `ε`'s corridor
and the prefix through `z` --- read at the node-`[153]` routing
(`K .coldFailureRouting`, a proposition, so its classified data is
canonical). -/
noncomputable def canonicalAbsorbedHandoff (data : Parameters)
    (object : Graph.FiniteObject.{u}) (epsilon : ColdEligibleHalfEdge data object) :
    Option (object.Vertex × Finset object.Vertex) := by
  classical
  exact if routing : ColdFailureRoutingStatement data object then
    canonicalChoice (fun pair : object.Vertex × Finset object.Vertex =>
      AbsorbedHandoffAt data object routing epsilon pair.1 pair.2)
  else none

/-- The first-high centre of one selected half-edge `ε`. -/
noncomputable def canonicalAbsorbedCentre (data : Parameters)
    (object : Graph.FiniteObject.{u}) (epsilon : ColdEligibleHalfEdge data object) :
    Option object.Vertex :=
  (canonicalAbsorbedHandoff data object epsilon).map Prod.fst

theorem canonicalAbsorbedHandoff_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {epsilon : ColdEligibleHalfEdge data object}
    (routing : ColdFailureRoutingStatement data object)
    (h : ∃ centre core, AbsorbedHandoffAt data object routing epsilon centre core) :
    ∃ centre core, canonicalAbsorbedHandoff data object epsilon = some (centre, core) ∧
      AbsorbedHandoffAt data object routing epsilon centre core := by
  classical
  obtain ⟨centre, core, holds⟩ := h
  obtain ⟨pair, pairEq, pairHolds⟩ :=
    canonicalChoice_spec (spec := fun pair : object.Vertex × Finset object.Vertex =>
      AbsorbedHandoffAt data object routing epsilon pair.1 pair.2)
      ⟨(centre, core), holds⟩
  refine ⟨pair.1, pair.2, ?_, pairHolds⟩
  simpa [canonicalAbsorbedHandoff, routing] using pairEq

theorem canonicalAbsorbedHandoff_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {epsilon : ColdEligibleHalfEdge data object}
    {centre : object.Vertex} {core : Finset object.Vertex}
    (h : canonicalAbsorbedHandoff data object epsilon = some (centre, core)) :
    ∃ routing : ColdFailureRoutingStatement data object,
      AbsorbedHandoffAt data object routing epsilon centre core := by
  classical
  unfold canonicalAbsorbedHandoff at h
  split at h
  · next routing =>
      exact ⟨routing, canonicalChoice_spec_of_eq_some
        (spec := fun pair : object.Vertex × Finset object.Vertex =>
          AbsorbedHandoffAt data object routing epsilon pair.1 pair.2) h⟩
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

/-- The absorbed Type B support at one selected half-edge `ε`: the prefix of its
corridor through its first high centre `z` (the counted core of node `[177]`'s
envelope) and `{z}`. -/
noncomputable def canonicalTypeBAbsorbedSupportAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (epsilon : ColdEligibleHalfEdge data object) :
    Option (Finset object.Vertex × Finset object.Vertex) :=
  (canonicalAbsorbedHandoff data object epsilon).map fun pair => (pair.2, {pair.1})

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

The same-token support is `canonicalSameTokenSupport`
(`Statements/CanonicalSameToken.lean`): the canonical choice of the
`∃ core centres, SameTokenHandoffAt data G core centres` body of node `[144]`.
It is defined after `Statements/SurplusPair.lean`, which this module does not
import. -/

end Hypostructure.Graph.Strategy.Spine

import Hypostructure.Graph.Statements.TypeBLanes
import Hypostructure.Graph.Contracts.RouteEight.Basic

/-!
# Contracts: the Type B support of the selected counterexample

Proof-agnostic facts about the lanes of `Statements/TypeBLanes.lean`: the
canonical Type B support `X = (Y_X, H_X)` of each entry form, its high centres,
the exclusivity of the lanes, and the combinators through which every Type B
fact and decision is evaluated at that one support.
-/

namespace Hypostructure.Graph.Contracts.TypeB

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## The canonical supports -/

theorem ordinarySupport_eq_some {core centres : Finset object.Vertex}
    (support : canonicalTypeBOrdinarySupport data object = some (core, centres)) :
    canonicalNegativePiece data object = some core ∧
      centres = Graph.TypeBRefinedSupport.centres object data.threshold core := by
  unfold canonicalTypeBOrdinarySupport at support
  obtain ⟨piece, pieceEq, pair⟩ := Option.map_eq_some_iff.mp support
  simp only [Prod.mk.injEq] at pair
  obtain ⟨rfl, rfl⟩ := pair
  exact ⟨pieceEq, rfl⟩

theorem decoratedSupport_eq_some {core centres : Finset object.Vertex}
    (support : canonicalTypeBDecoratedSupport data object = some (core, centres)) :
    canonicalNegativePiece data object = some core ∧
      ∃ separator, canonicalHandoffSeparatorAt data object core = some separator ∧
        centres = {separator} := by
  unfold canonicalTypeBDecoratedSupport at support
  obtain ⟨piece, pieceEq, inner⟩ := Option.bind_eq_some_iff.mp support
  obtain ⟨separator, separatorEq, pair⟩ := Option.map_eq_some_iff.mp inner
  simp only [Prod.mk.injEq] at pair
  obtain ⟨rfl, rfl⟩ := pair
  exact ⟨pieceEq, separator, separatorEq, rfl⟩

/-- The canonical decorated envelope has core `X₀` and decorations `{z}`, where
`z` is the canonical surviving separator of `X₀`. -/
theorem decoratedEnvelope_eq_some
    {envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK
      (handoffHighDegree data object)
      (handoffAbsorbing data object (canonicalWindowPacking data object))}
    (selected : canonicalTypeBDecoratedEnvelope data object = some envelope) :
    ∃ core, canonicalNegativePiece data object = some core ∧ envelope.core = core ∧
      ∃ separator, canonicalHandoffSeparatorAt data object core = some separator ∧
        envelope.decorations = {separator} := by
  classical
  unfold canonicalTypeBDecoratedEnvelope at selected
  obtain ⟨core, coreEq, atCore⟩ := Option.bind_eq_some_iff.mp selected
  refine ⟨core, coreEq, canonicalHandoffEnvelopeAt_core atCore, ?_⟩
  unfold canonicalHandoffEnvelopeAt at atCore
  split at atCore
  · obtain ⟨separated, separatedEq, built⟩ := Option.bind_eq_some_iff.mp atCore
    split at built
    · cases built
      refine ⟨separated.2.separation.separator, ?_, ?_⟩
      · simp [canonicalHandoffSeparatorAt, separatedEq]
      · exact ExitSevenSeparation.envelope_decorations _ _ _ _
    · cases built
  · cases atCore

theorem absorbedSupport_eq_some {epsilon : ColdEligibleHalfEdge data object}
    {core centres : Finset object.Vertex}
    (support : canonicalTypeBAbsorbedSupport data object epsilon =
      some (core, centres)) :
    ∃ centre, canonicalAbsorbedCentre data object epsilon = some centre ∧
      centres = {centre} := by
  classical
  unfold canonicalTypeBAbsorbedSupport at support
  split at support
  · obtain ⟨centre, centreEq, pair⟩ := Option.map_eq_some_iff.mp support
    simp only [Prod.mk.injEq] at pair
    exact ⟨centre, centreEq, pair.2.symm⟩
  · cases support

/-- The first-high centre of an absorbed germ is high. -/
theorem absorbedCentre_high {epsilon : ColdEligibleHalfEdge data object}
    {centre : object.Vertex}
    (selected : canonicalAbsorbedCentre data object epsilon = some centre) :
    Graph.IsHighCentre object data.threshold centre := by
  obtain ⟨_routing, witness⟩ := canonicalAbsorbedCentre_spec_of_eq_some selected
  rcases witness with ⟨_routing', _epsilon', _germEq, _firstIndex, _centreEq,
    _indexLe, high, _tail⟩
  exact high

/-! ## Lane membership -/

/-- `(Y, H)` is the Type B support of `G` in one of the continuation lanes. -/
def TypeBLaneMember (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex) : Prop :=
  TypeBOrdinaryLane data object core centres ∨
    TypeBDecoratedLane data object core centres ∨
    ∃ epsilon, TypeBAbsorbedLane data object epsilon core centres

/-- On the ordinary and decorated lanes the core is the canonical negative piece
`X₀` of `P₀`, it is negative, and its own high centres are assigned. -/
def TypeBCanonicalLane (data : Parameters) (object : Graph.FiniteObject.{u})
    (core centres : Finset object.Vertex) : Prop :=
  ∃ component, canonicalNegativeComponent data object = some component ∧
    component ∈ object.canonicalPieces (canonicalRemainder data object) ∧
    object.pieceSupport (canonicalRemainder data object) component = core ∧
    object.NegativeNetCharge core data.threshold data.dischargeScale ∧
    Graph.TypeBRefinedSupport.centres object data.threshold core ⊆ centres

theorem canonicalLane_of_piece {core centres : Finset object.Vertex}
    (piece : canonicalNegativePiece data object = some core)
    (subset : Graph.TypeBRefinedSupport.centres object data.threshold core ⊆
      centres) :
    TypeBCanonicalLane data object core centres := by
  obtain ⟨component, componentEq, pieceEq⟩ :=
    canonicalNegativePiece_eq_some_iff.mp piece
  obtain ⟨member, negative⟩ :=
    canonicalNegativeComponent_spec_of_eq_some componentEq
  refine ⟨component, componentEq, member, pieceEq, ?_, subset⟩
  rw [← pieceEq]
  exact negative

theorem TypeBOrdinaryLane.canonical {core centres : Finset object.Vertex}
    (lane : TypeBOrdinaryLane data object core centres) :
    TypeBCanonicalLane data object core centres := by
  obtain ⟨_cap, support, _positive⟩ := lane
  obtain ⟨piece, rfl⟩ := ordinarySupport_eq_some support
  exact canonicalLane_of_piece piece (Finset.Subset.refl _)

theorem centres_eq_empty_of_ambientSurplus_eq_zero {core : Finset object.Vertex}
    (zero : object.ambientSurplus core data.threshold = 0) :
    Graph.TypeBRefinedSupport.centres object data.threshold core = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro centre member
  obtain ⟨inCore, high⟩ := Graph.TypeBRefinedSupport.mem_centres.mp member
  have : object.degree centre - data.threshold = 0 := by
    unfold Graph.FiniteObject.ambientSurplus at zero
    exact Finset.sum_eq_zero_iff.mp zero centre inCore
  simp only [Graph.IsHighCentre] at high
  omega

theorem TypeBDecoratedLane.canonical {core centres : Finset object.Vertex}
    (lane : TypeBDecoratedLane data object core centres) :
    TypeBCanonicalLane data object core centres := by
  obtain ⟨_cap, support, zero, _envelope⟩ := lane
  obtain ⟨piece, _separator⟩ := decoratedSupport_eq_some support
  refine canonicalLane_of_piece piece ?_
  rw [centres_eq_empty_of_ambientSurplus_eq_zero zero]
  exact Finset.empty_subset _

theorem TypeBOrdinaryLane.high {core centres : Finset object.Vertex}
    (lane : TypeBOrdinaryLane data object core centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre := by
  obtain ⟨_cap, support, _positive⟩ := lane
  obtain ⟨_piece, rfl⟩ := ordinarySupport_eq_some support
  exact Graph.TypeBRefinedSupport.centres_high object data.threshold core

theorem TypeBDecoratedLane.envelope {core centres : Finset object.Vertex}
    (lane : TypeBDecoratedLane data object core centres) :
    ∃ envelope, canonicalTypeBDecoratedEnvelope data object = some envelope ∧
      envelope.core = core ∧ envelope.decorations = centres := by
  obtain ⟨_cap, support, _zero, isSome⟩ := lane
  obtain ⟨envelope, envelopeEq⟩ := Option.isSome_iff_exists.mp isSome
  obtain ⟨piece, separator, separatorEq, rfl⟩ :=
    decoratedSupport_eq_some support
  obtain ⟨core', coreEq', envelopeCore, separator', separatorEq', decorations⟩ :=
    decoratedEnvelope_eq_some envelopeEq
  rw [piece, Option.some.injEq] at coreEq'
  subst coreEq'
  rw [separatorEq, Option.some.injEq] at separatorEq'
  subst separatorEq'
  exact ⟨envelope, envelopeEq, envelopeCore, decorations⟩

theorem TypeBDecoratedLane.high {core centres : Finset object.Vertex}
    (lane : TypeBDecoratedLane data object core centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre := by
  obtain ⟨envelope, _envelopeEq, _core, rfl⟩ := TypeBDecoratedLane.envelope lane
  intro centre member
  exact envelope.decorations_high centre member

theorem TypeBAbsorbedLane.high {epsilon : ColdEligibleHalfEdge data object}
    {core centres : Finset object.Vertex}
    (lane : TypeBAbsorbedLane data object epsilon core centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre := by
  obtain ⟨_routing, _notCandidate, support⟩ := lane
  obtain ⟨centre, centreEq, rfl⟩ := absorbedSupport_eq_some support
  intro vertex member
  rw [Finset.mem_singleton] at member
  subst member
  exact absorbedCentre_high centreEq

theorem TypeBLaneMember.high {core centres : Finset object.Vertex}
    (member : TypeBLaneMember data object core centres) :
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre := by
  rcases member with lane | lane | ⟨_epsilon, lane⟩
  · exact TypeBOrdinaryLane.high lane
  · exact TypeBDecoratedLane.high lane
  · exact TypeBAbsorbedLane.high lane

/-! ## Exclusivity of the lanes -/

/-- The net-cap arm and the failed-collision arm of `[57]`/`[173]` are exact
complements. -/
theorem netChargeCap_not_exactCollisionFails
    (cap : NetChargeCapStatement data object)
    (fails : ExactCollisionFailsStatement data object) : False := by
  obtain ⟨packing, valid, card, nonnegative⟩ := fails
  exact (object.not_negativeNetCharge_iff _ data.threshold data.dischargeScale).mpr
    nonnegative (cap packing valid card)

theorem ordinary_decorated_exclusive
    {core centres core' centres' : Finset object.Vertex}
    (ordinary : TypeBOrdinaryLane data object core centres)
    (decorated : TypeBDecoratedLane data object core' centres') : False := by
  obtain ⟨_cap, support, positive⟩ := ordinary
  obtain ⟨_cap', support', zero, _envelope⟩ := decorated
  obtain ⟨piece, _⟩ := ordinarySupport_eq_some support
  obtain ⟨piece', _⟩ := decoratedSupport_eq_some support'
  rw [piece, Option.some.injEq] at piece'
  subst piece'
  omega

theorem ordinary_absorbed_exclusive {core centres : Finset object.Vertex}
    (ordinary : TypeBOrdinaryLane data object core centres)
    (entered : TypeBAbsorbedEntered data object) : False :=
  netChargeCap_not_exactCollisionFails ordinary.1 entered.1

theorem decorated_absorbed_exclusive {core centres : Finset object.Vertex}
    (decorated : TypeBDecoratedLane data object core centres)
    (entered : TypeBAbsorbedEntered data object) : False :=
  netChargeCap_not_exactCollisionFails decorated.1 entered.1

theorem ordinary_unique {core centres core' centres' : Finset object.Vertex}
    (first : TypeBOrdinaryLane data object core centres)
    (second : TypeBOrdinaryLane data object core' centres') :
    core = core' ∧ centres = centres' := by
  have := first.2.1.symm.trans second.2.1
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem decorated_unique {core centres core' centres' : Finset object.Vertex}
    (first : TypeBDecoratedLane data object core centres)
    (second : TypeBDecoratedLane data object core' centres') :
    core = core' ∧ centres = centres' := by
  have := first.2.1.symm.trans second.2.1
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

/-! ## The lane combinators -/

theorem TypeBLaneAll.imp {P Q : Finset object.Vertex → Finset object.Vertex → Prop}
    (step : ∀ core centres, TypeBLaneMember data object core centres →
      P core centres → Q core centres)
    (fact : TypeBLaneAll data object P) : TypeBLaneAll data object Q := by
  rcases fact with ⟨core, centres, lane, holds⟩ | ⟨core, centres, lane, holds⟩ |
      ⟨entered, holds⟩
  · exact Or.inl ⟨core, centres, lane, step core centres (Or.inl lane) holds⟩
  · exact Or.inr (Or.inl ⟨core, centres, lane,
      step core centres (Or.inr (Or.inl lane)) holds⟩)
  · exact Or.inr (Or.inr ⟨entered, fun epsilon core centres lane =>
      step core centres (Or.inr (Or.inr ⟨epsilon, lane⟩))
        (holds epsilon core centres lane)⟩)

theorem TypeBLaneSome.imp {P Q : Finset object.Vertex → Finset object.Vertex → Prop}
    (step : ∀ core centres, TypeBLaneMember data object core centres →
      P core centres → Q core centres)
    (fact : TypeBLaneSome data object P) : TypeBLaneSome data object Q := by
  rcases fact with ⟨core, centres, lane, holds⟩ | ⟨core, centres, lane, holds⟩ |
      ⟨entered, epsilon, core, centres, lane, holds⟩
  · exact Or.inl ⟨core, centres, lane, step core centres (Or.inl lane) holds⟩
  · exact Or.inr (Or.inl ⟨core, centres, lane,
      step core centres (Or.inr (Or.inl lane)) holds⟩)
  · exact Or.inr (Or.inr ⟨entered, epsilon, core, centres, lane,
      step core centres (Or.inr (Or.inr ⟨epsilon, lane⟩)) holds⟩)

/-- Two facts at the Type B support of `G` hold together at that support: the
lanes are exclusive and each lane's support is unique. -/
theorem TypeBLaneAll.and {P Q : Finset object.Vertex → Finset object.Vertex → Prop}
    (first : TypeBLaneAll data object P) (second : TypeBLaneAll data object Q) :
    TypeBLaneAll data object (fun core centres => P core centres ∧ Q core centres) := by
  rcases first with ⟨core, centres, lane, holds⟩ | ⟨core, centres, lane, holds⟩ |
      ⟨entered, holds⟩ <;>
    rcases second with ⟨core', centres', lane', holds'⟩ |
      ⟨core', centres', lane', holds'⟩ | ⟨entered', holds'⟩
  · obtain ⟨rfl, rfl⟩ := ordinary_unique lane lane'
    exact Or.inl ⟨core, centres, lane, holds, holds'⟩
  · exact (ordinary_decorated_exclusive lane lane').elim
  · exact (ordinary_absorbed_exclusive lane entered').elim
  · exact (ordinary_decorated_exclusive lane' lane).elim
  · obtain ⟨rfl, rfl⟩ := decorated_unique lane lane'
    exact Or.inr (Or.inl ⟨core, centres, lane, holds, holds'⟩)
  · exact (decorated_absorbed_exclusive lane entered').elim
  · exact (ordinary_absorbed_exclusive lane' entered).elim
  · exact (decorated_absorbed_exclusive lane' entered).elim
  · exact Or.inr (Or.inr ⟨entered, fun epsilon core centres lane =>
      ⟨holds epsilon core centres lane, holds' epsilon core centres lane⟩⟩)

/-- A fact at the Type B support of `G` holds at the support of a positive
decision arm. -/
theorem TypeBLaneSome.and_all
    {P Q : Finset object.Vertex → Finset object.Vertex → Prop}
    (first : TypeBLaneSome data object P) (second : TypeBLaneAll data object Q) :
    TypeBLaneSome data object (fun core centres => P core centres ∧ Q core centres) := by
  rcases first with ⟨core, centres, lane, holds⟩ | ⟨core, centres, lane, holds⟩ |
      ⟨entered, epsilon, core, centres, lane, holds⟩ <;>
    rcases second with ⟨core', centres', lane', holds'⟩ |
      ⟨core', centres', lane', holds'⟩ | ⟨entered', holds'⟩
  · obtain ⟨rfl, rfl⟩ := ordinary_unique lane lane'
    exact Or.inl ⟨core, centres, lane, holds, holds'⟩
  · exact (ordinary_decorated_exclusive lane lane').elim
  · exact (ordinary_absorbed_exclusive lane entered').elim
  · exact (ordinary_decorated_exclusive lane' lane).elim
  · obtain ⟨rfl, rfl⟩ := decorated_unique lane lane'
    exact Or.inr (Or.inl ⟨core, centres, lane, holds, holds'⟩)
  · exact (decorated_absorbed_exclusive lane entered').elim
  · exact (ordinary_absorbed_exclusive lane' entered).elim
  · exact (decorated_absorbed_exclusive lane' entered).elim
  · exact Or.inr (Or.inr ⟨entered, epsilon, core, centres, lane, holds,
      holds' epsilon core centres lane⟩)

/-- **The decision split at the Type B support of `G`**: on the lane of the
predecessor fact, `P` holds at the lane's support (at some absorbed support), or
fails at it (at every absorbed support).  The two conclusions are exact
complements on that support (`TypeBLaneSome.not_all`). -/
theorem TypeBLaneAll.split {Q : Finset object.Vertex → Finset object.Vertex → Prop}
    (P : Finset object.Vertex → Finset object.Vertex → Prop)
    (fact : TypeBLaneAll data object Q) :
    TypeBLaneSome data object (fun core centres => Q core centres ∧ P core centres) ∨
      TypeBLaneAll data object
        (fun core centres => Q core centres ∧ ¬ P core centres) := by
  classical
  rcases fact with ⟨core, centres, lane, holds⟩ | ⟨core, centres, lane, holds⟩ |
      ⟨entered, holds⟩
  · by_cases positive : P core centres
    · exact Or.inl (Or.inl ⟨core, centres, lane, holds, positive⟩)
    · exact Or.inr (Or.inl ⟨core, centres, lane, holds, positive⟩)
  · by_cases positive : P core centres
    · exact Or.inl (Or.inr (Or.inl ⟨core, centres, lane, holds, positive⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨core, centres, lane, holds, positive⟩))
  · by_cases positive : ∃ epsilon core centres,
        TypeBAbsorbedLane data object epsilon core centres ∧ P core centres
    · obtain ⟨epsilon, core, centres, lane, holds'⟩ := positive
      exact Or.inl (Or.inr (Or.inr ⟨entered, epsilon, core, centres, lane,
        holds epsilon core centres lane, holds'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨entered, fun epsilon core centres lane =>
        ⟨holds epsilon core centres lane,
          fun holds' => positive ⟨epsilon, core, centres, lane, holds'⟩⟩⟩))

/-- A positive decision arm names a lane support where its predicate holds. -/
theorem TypeBLaneSome.exists {P : Finset object.Vertex → Finset object.Vertex → Prop}
    (fact : TypeBLaneSome data object P) :
    ∃ core centres, TypeBLaneMember data object core centres ∧ P core centres := by
  rcases fact with ⟨core, centres, lane, holds⟩ | ⟨core, centres, lane, holds⟩ |
      ⟨_entered, epsilon, core, centres, lane, holds⟩
  · exact ⟨core, centres, Or.inl lane, holds⟩
  · exact ⟨core, centres, Or.inr (Or.inl lane), holds⟩
  · exact ⟨core, centres, Or.inr (Or.inr ⟨epsilon, lane⟩), holds⟩

/-- The two arms of a decision at the Type B support of `G` exclude each
other. -/
theorem TypeBLaneSome.not_all {P : Finset object.Vertex → Finset object.Vertex → Prop}
    (positive : TypeBLaneSome data object P)
    (negative : TypeBLaneAll data object fun core centres => ¬ P core centres) :
    False := by
  obtain ⟨_core, _centres, _member, both⟩ :=
    TypeBLaneSome.exists (TypeBLaneSome.and_all positive negative)
  exact both.2 both.1

/-! ## The B2 disjoint choice -/

/-- A disjoint choice at the assigned centres restricts to every demand
subfamily. -/
theorem hasDisjointChoice_mono
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece assigned demands : Finset object.Vertex}
    (subset : demands ⊆ assigned)
    (choice : Graph.TypeBRefinedSupport.HasDisjointChoice object threshold
      dischargeScale packing piece assigned assigned) :
    Graph.TypeBRefinedSupport.HasDisjointChoice object threshold dischargeScale
      packing piece assigned demands := by
  obtain ⟨choice⟩ := choice
  exact ⟨{
    entry := fun hub member => choice.entry hub (subset member)
    eligible := fun hub member => choice.eligible hub (subset member)
    carrierDisjoint := fun left leftMem right rightMem different =>
      choice.carrierDisjoint left (subset leftMem) right (subset rightMem) different
    reserveDisjoint := fun left leftMem right rightMem different =>
      choice.reserveDisjoint left (subset leftMem) right (subset rightMem)
        different }⟩

/-- `lem:typeB-bridge-to-overlap`, both directions: at high assigned centres, a
disjoint choice fails exactly when a minimal overlap obstruction exists. -/
theorem not_hasDisjointChoice_iff_overlapObstruction
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece assigned : Finset object.Vertex}
    (high : ∀ hub ∈ assigned, Graph.IsHighCentre object threshold hub) :
    ¬ Graph.TypeBRefinedSupport.HasDisjointChoice object threshold dischargeScale
        packing piece assigned assigned ↔
      Nonempty (Graph.TypeBRefinedSupport.OverlapObstruction object threshold
        dischargeScale packing piece assigned) := by
  constructor
  · exact Graph.TypeBRefinedSupport.exists_overlapObstruction_of_not_hasDisjointChoice
      object threshold dischargeScale packing piece assigned high
  · rintro ⟨obstruction⟩ choice
    exact obstruction.noDisjointChoice
      (hasDisjointChoice_mono obstruction.demands_subset choice)

/-- The canonical B2 choice exists when the disjoint choice does. -/
theorem canonicalTypeBChoice_spec {core centres : Finset object.Vertex}
    (choice : Graph.TypeBRefinedSupport.HasDisjointChoice object data.threshold
      data.dischargeScale (canonicalWindowPacking data object) core centres
      centres) :
    ∃ selected, canonicalTypeBChoice data object core centres = some selected := by
  classical
  exact ⟨Classical.choice choice, by simp [canonicalTypeBChoice, choice]⟩

/-- The canonical B2 ledger exists when the choice does, the centres are high,
and they contain the core's own high centres. -/
theorem canonicalTypeBDisjointChoice_spec {core centres : Finset object.Vertex}
    (spec : TypeBLedgerSpec data object core centres) :
    ∃ ledger, canonicalTypeBDisjointChoice data object core centres = some ledger :=
  Option.isSome_iff_exists.mp (canonicalTypeBDisjointChoice_isSome_iff.mpr spec)

end Hypostructure.Graph.Contracts.TypeB

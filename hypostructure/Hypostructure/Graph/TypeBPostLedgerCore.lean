import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.TypeABCertificate
import Hypostructure.Graph.TypeBEnvelopeCharge
import Hypostructure.Graph.ReceiverRouting

/-!
# Post-ledger Type A core hygiene

This is the generic mathematical content of
`lem:typeB-postledger-core-hygiene`.  It decomposes the literal remaining core
of the canonical `TypeBRefinedSupport.DisjointLedger`; no legacy residual, receiver
classification, Type A outcome, or routing payload is introduced here.
-/

namespace Hypostructure.Graph.TypeBPostLedgerCore

open Hypostructure.Graph
open Hypostructure.Graph.SupportComponents

universe u v w

variable {object : FiniteObject.{u}}

noncomputable section

local instance (priority := low) {α : Type w} : DecidableEq α :=
  Classical.decEq α

/-! ## Heredity along an induced restriction

The manuscript's first sentence -- "the remaining non-window core is an induced
subgraph of the original remainder core after deleting a declared family of
ledger carriers" -- is `FiniteObject.induce` on a smaller support.  The two
hereditary clauses below are *proved* from that induced-subgraph structure. -/

/-- The canonical induced embedding of a smaller support into a larger one.
Both sides are `FiniteObject.induce` of the *same* ambient object, so adjacency
on either side is ambient adjacency of the underlying vertices and the embedding
reflects it on the nose. -/
def inducedSubsetEmbedding (object : FiniteObject.{u})
    {small large : Finset object.Vertex} (subset : small ⊆ large) :
    (object.induce small).graph ↪g (object.induce large).graph :=
  ⟨⟨fun vertex => ⟨vertex.1, subset vertex.2⟩, by
      intro left right equal
      refine Subtype.ext ?_
      exact congrArg (fun v : {x : object.Vertex // x ∈ large} => v.1) equal⟩,
    Iff.rfl⟩

/-- **Heredity of induced-obstruction freeness.**  An induced copy of a pattern
inside the smaller support is an induced copy inside the larger one, so freeness
descends.  Nothing is assumed: this is the composition of two induced
embeddings. -/
theorem inducedObstructionFree_of_subset {PatternVertex : Type w}
    (pattern : SimpleGraph PatternVertex) {small large : Finset object.Vertex}
    (subset : small ⊆ large)
    (free : InducedObstructionFree pattern (object.induce large)) :
    InducedObstructionFree pattern (object.induce small) := by
  intro copy
  exact free (copy.trans ⟨inducedSubsetEmbedding object subset⟩)

/-- **`P₁₃`-freeness is hereditary** (manuscript invariant 22).  The `P₁₃` case
is `order = 13`. -/
theorem inducedPathFree_of_subset {small large : Finset object.Vertex}
    (order : Nat) (subset : small ⊆ large)
    (free : InducedPathFree (object.induce large) order) :
    InducedPathFree (object.induce small) order :=
  inducedObstructionFree_of_subset _ subset free

/-! ## The connected components of a counted support

`SupportComponents.Connected` already owns the connected components of an
induced support and their disjoint coverage law; the only thing added here is
that a weight sums over the support blockwise. -/

/-- A weight on a counted support is the sum of its blockwise weights over the
connected components of the induced restriction.  This is
`SupportComponents.Connected.mem_support_iff_mem_component_with_vertices`
together with `disjoint_vertices`; components are treated separately, exactly as
the manuscript demands. -/
theorem sum_eq_sum_components {Weight : Type w} [AddCommMonoid Weight]
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (weight : object.Vertex → Weight) :
    ∑ y ∈ support, weight y
      = ((Connected.order object support).map fun component =>
          ∑ y ∈ Connected.vertices object support component, weight y).sum := by
  classical
  rw [← List.sum_toFinset _ (Connected.order_nodup object support)]
  have disjoint : Set.PairwiseDisjoint
      ((Connected.order object support).toFinset :
        Set (Connected.Component object support))
      (Connected.vertices object support) := by
    intro a _ b _ different
    exact Connected.disjoint_vertices object support different
  rw [← Finset.sum_biUnion (f := weight) disjoint]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext y
  simp only [Finset.mem_biUnion, List.mem_toFinset]
  exact Connected.mem_support_iff_mem_component_with_vertices object support y

/-! ## The canonical live B2 post-ledger core -/

variable {threshold dischargeScale : Nat}
variable {packing : Finset (Finset object.Vertex)}
variable {piece : TypeBRefinedSupport.CanonicalPiece object packing}

/-- A canonical component is literally contained in the one remaining core. -/
theorem refinedComponent_subset_remainingCore
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) :
    Connected.vertices object ledger.remainingCore component ⊆
      ledger.remainingCore := by
  intro vertex member
  exact ((Connected.mem_vertices_iff object ledger.remainingCore component vertex).1
    member).1

/-- A post-ledger component remains in the incoming assigned support. -/
theorem refinedComponent_subset_piece
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) :
    Connected.vertices object ledger.remainingCore component ⊆ piece.vertices := by
  intro vertex member
  exact ledger.remainingCore_subset
    (((Connected.mem_vertices_iff object ledger.remainingCore component vertex).1
      member).1)

/-- A component in the canonical order is connected in the ambient object. -/
theorem refinedComponent_connected
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore)
    (member : component ∈ Connected.order object ledger.remainingCore) :
    Connected.ConnectedOn object
      (Connected.vertices object ledger.remainingCore component) := by
  simpa [Connected.vertices] using
    Connected.connectedOn_of_mem_order object ledger.remainingCore member

/-- B2(d) is inherited by every canonical remainder component. -/
theorem refinedComponent_has_no_highCentre
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore)
    {vertex : object.Vertex}
    (member : vertex ∈ Connected.vertices object ledger.remainingCore component) :
    ¬ Graph.IsHighCentre object threshold vertex := by
  apply ledger.noHighCentre_remaining
  exact ((Connected.mem_vertices_iff object ledger.remainingCore component vertex).1
    member).1

/-- The exact unconsumed ordinary-reserve units whose remainder-side anchor
lies in one canonical post-ledger component.  This replaces the former raw
count of deleted neighbouring vertices. -/
noncomputable def refinedComponentReserveUnits
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) :
    Finset (OrdinaryDeficiencyReserve.Carrier object) :=
  OrdinaryDeficiencyReserve.anchorFibre ledger.remainingReserve
    (Connected.vertices object ledger.remainingCore component)

theorem refinedComponentReserveUnits_subset
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) :
    refinedComponentReserveUnits ledger component ⊆ ledger.remainingReserve :=
  OrdinaryDeficiencyReserve.anchorFibre_subset _ _

/-- The exact weighted component reserve.  Positive-deficiency units have full
capacity `2s`; packed-window incidences have half capacity `s`. -/
noncomputable def refinedComponentReserve
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) : Int :=
  OrdinaryDeficiencyReserve.capacity dischargeScale
    (refinedComponentReserveUnits ledger component)

theorem refinedComponentReserve_nonneg
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) :
    0 ≤ refinedComponentReserve ledger component := by
  exact OrdinaryDeficiencyReserve.capacity_nonnegative _ _

/-- The component's literal window-stub capacity.  This is the scaled boundary
incidence supplied by `lem:stub-positive`; it is not stored as an authored
capacity ledger. -/
noncomputable def refinedComponentWindowStubReserve
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) : Int :=
  ((dischargeScale * object.boundaryIncidence
    (Connected.vertices object ledger.remainingCore component) : Nat) : Int)

/-- Positive deficiency of a post-ledger component is supplied by the unused
ordinary reserve anchored in that component together with its literal boundary
stub reserve. -/
theorem refinedComponent_positiveDeficiency_supplied
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    ((dischargeScale * object.positiveDeficiency
      (Connected.vertices object ledger.remainingCore component)
      threshold : Nat) : Int) ≤
      refinedComponentReserve ledger component +
        refinedComponentWindowStubReserve ledger component := by
  have demand := object.positiveDeficiency_le_boundaryIncidence
    (Connected.vertices object ledger.remainingCore component) threshold baseline
  have scaled := Nat.mul_le_mul_left dischargeScale demand
  have scaledInt :
      ((dischargeScale * object.positiveDeficiency
        (Connected.vertices object ledger.remainingCore component)
        threshold : Nat) : Int) ≤
      ((dischargeScale * object.boundaryIncidence
        (Connected.vertices object ledger.remainingCore component) : Nat) : Int) := by
    exact_mod_cast scaled
  have reserveNonnegative := refinedComponentReserve_nonneg ledger component
  unfold refinedComponentWindowStubReserve
  linarith

/-- The unconsumed reserve units anchored anywhere in the literal post-ledger
core. -/
noncomputable def refinedRemainingReserveUnits
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    Finset (OrdinaryDeficiencyReserve.Carrier object) :=
  OrdinaryDeficiencyReserve.anchorFibre ledger.remainingReserve
    ledger.remainingCore

theorem refinedRemainingReserveUnits_subset
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    refinedRemainingReserveUnits ledger ⊆ ledger.remainingReserve :=
  OrdinaryDeficiencyReserve.anchorFibre_subset _ _

/-- The reserve anchored in the remaining core is the exact disjoint union of
the fibres anchored in its canonical connected components. -/
theorem refinedRemainingReserveUnits_eq_biUnion_components
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    refinedRemainingReserveUnits ledger =
      (Connected.order object ledger.remainingCore).toFinset.biUnion
        fun component => refinedComponentReserveUnits ledger component := by
  classical
  have cover :
      (Connected.order object ledger.remainingCore).toFinset.biUnion
          (Connected.vertices object ledger.remainingCore) =
        ledger.remainingCore := by
    ext vertex
    simp only [Finset.mem_biUnion, List.mem_toFinset]
    exact (Connected.mem_support_iff_mem_component_with_vertices
      object ledger.remainingCore vertex).symm
  rw [refinedRemainingReserveUnits]
  calc
    OrdinaryDeficiencyReserve.anchorFibre ledger.remainingReserve
        ledger.remainingCore =
      OrdinaryDeficiencyReserve.anchorFibre ledger.remainingReserve
        ((Connected.order object ledger.remainingCore).toFinset.biUnion
          (Connected.vertices object ledger.remainingCore)) :=
      congrArg (OrdinaryDeficiencyReserve.anchorFibre ledger.remainingReserve)
        cover.symm
    _ = (Connected.order object ledger.remainingCore).toFinset.biUnion
          fun component => OrdinaryDeficiencyReserve.anchorFibre
            ledger.remainingReserve
            (Connected.vertices object ledger.remainingCore component) :=
      OrdinaryDeficiencyReserve.anchorFibre_biUnion ledger.remainingReserve
        (Connected.order object ledger.remainingCore).toFinset
        (Connected.vertices object ledger.remainingCore)
    _ = (Connected.order object ledger.remainingCore).toFinset.biUnion
          fun component => refinedComponentReserveUnits ledger component := by
      rfl

/-- Exact capacity additivity over the canonical connected components. -/
theorem refinedRemainingReserveCapacity_eq_sum_components
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    OrdinaryDeficiencyReserve.capacity dischargeScale
        (refinedRemainingReserveUnits ledger) =
      ∑ component ∈ (Connected.order object ledger.remainingCore).toFinset,
        refinedComponentReserve ledger component := by
  classical
  rw [refinedRemainingReserveUnits_eq_biUnion_components]
  apply OrdinaryDeficiencyReserve.capacity_biUnion
  intro left _leftMember right _rightMember distinct
  exact OrdinaryDeficiencyReserve.anchorFibre_disjoint
    (Connected.disjoint_vertices object ledger.remainingCore distinct)

/-- The indexed reserve split used downstream is literal and lossless. -/
theorem consumed_union_remainingReserve
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    ledger.consumedReserveUnits ∪ ledger.remainingReserve =
      object.ordinaryDeficiencyReserve threshold packing piece.vertices :=
  ledger.consumed_union_remainingReserve

/-- Exact vertex-charge decomposition into the removed B2 support and the
canonical connected components of the remainder. -/
theorem refinedCoreChargePartition
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    ∑ vertex ∈ piece.vertices,
        TypeBRefinedSupport.scaledCoreCharge object threshold dischargeScale
          piece.vertices vertex =
      (∑ vertex ∈ ledger.removedVertices,
        TypeBRefinedSupport.scaledCoreCharge object threshold dischargeScale
          piece.vertices vertex) +
      ((Connected.order object ledger.remainingCore).map fun component =>
        ∑ vertex ∈ Connected.vertices object ledger.remainingCore component,
          TypeBRefinedSupport.scaledCoreCharge object threshold dischargeScale
          piece.vertices vertex).sum := by
  classical
  have removedSubset : ledger.removedVertices ⊆ piece.vertices := by
    change TypeBRefinedSupport.centres object threshold piece.vertices ∪
      ledger.chargedVertexSupport ⊆ piece.vertices
    exact fun {_vertex} member => (Finset.mem_union.mp member).elim
      (fun centre => TypeBRefinedSupport.centres_subset centre)
      (fun charged => ledger.chargedVertexSupport_subset charged)
  have complement : piece.vertices \ ledger.remainingCore = ledger.removedVertices := by
    rw [TypeBRefinedSupport.DisjointLedger.remainingCore]
    exact Finset.sdiff_sdiff_eq_self removedSubset
  have split := Finset.sum_sdiff ledger.remainingCore_subset
    (f := fun vertex => TypeBRefinedSupport.scaledCoreCharge object threshold
      dischargeScale piece.vertices vertex)
  have components := sum_eq_sum_components object ledger.remainingCore
    (TypeBRefinedSupport.scaledCoreCharge object threshold dischargeScale
          piece.vertices)
  rw [complement, components] at split
  linarith

/-- Exact augmented-ledger decomposition over the same remainder. -/
theorem refinedAugmentedLedgerPartition
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    TypeBRefinedSupport.augmentedLedger object threshold dischargeScale piece.vertices =
      (∑ vertex ∈ ledger.removedVertices,
        TypeBRefinedSupport.scaledCoreCharge object threshold dischargeScale
          piece.vertices vertex) +
      ((Connected.order object ledger.remainingCore).map fun component =>
        ∑ vertex ∈ Connected.vertices object ledger.remainingCore component,
          TypeBRefinedSupport.scaledCoreCharge object threshold dischargeScale
          piece.vertices vertex).sum +
      ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece.vertices,
        TypeBRefinedSupport.scaledCentreCharge object threshold dischargeScale
          centre := by
  rw [TypeBRefinedSupport.augmentedLedger, refinedCoreChargePartition ledger]

/-! ## `lem:typeB-postledger-core-hygiene` -/

theorem hereditarilyTargetUncompressible_of_subset
    {presentation : TypeAB.Presentation.{u}}
    {small large : Finset object.Vertex}
    (subset : small ⊆ large)
    (uncompressible :
      TypeAB.HereditarilyTargetUncompressible presentation object large) :
    TypeAB.HereditarilyTargetUncompressible presentation object small := by
  intro inner nonempty proper baseline
  apply uncompressible inner nonempty
  · refine Finset.ssubset_iff_subset_ne.mpr
      ⟨proper.subset.trans subset, ?_⟩
    intro equality
    have cardLt := Finset.card_lt_card proper
    have cardLe := Finset.card_le_card subset
    rw [← equality] at cardLe
    omega
  · exact baseline

theorem refinedComponent_ambientSurplus_eq_zero
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) :
    object.ambientSurplus
      (Connected.vertices object ledger.remainingCore component) threshold = 0 := by
  classical
  unfold FiniteObject.ambientSurplus
  apply Finset.sum_eq_zero
  intro vertex member
  have notHigh := refinedComponent_has_no_highCentre ledger component member
  have degreeLe : object.degree vertex ≤ threshold := by
    simpa [Graph.IsHighCentre] using notHigh
  exact Nat.sub_eq_zero_of_le degreeLe

/-- The remainder-normalization invariant, restricted to one post-ledger
component, is exactly the empty internal baseline core used by receiver
routing. -/
theorem emptyInternalThreeCore_of_noBaselineSubsupport
    {presentation : TypeAB.Presentation.{u}}
    {support : Finset object.Vertex}
    (baselineDegree : threshold = presentation.baselineDegree)
    (noBaselineSubsupport : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ MinimumDegreeAtLeast threshold (object.induce inner)) :
    TypeAB.EmptyInternalThreeCore presentation object support := by
  rintro ⟨inner, subset, _nonempty, baseline⟩
  apply noBaselineSubsupport inner subset
  rw [baselineDegree]
  exact baseline

/-- One exact paper component of the post-ledger core.  Every field is either
an inherited admissibility fact or a theorem of the canonical B2 ledger. -/
structure PostLedgerComponent
    (presentation : TypeAB.Presentation.{u})
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore) : Prop where
  componentMember : component ∈ Connected.order object ledger.remainingCore
  containedInRemainingCore :
    Connected.vertices object ledger.remainingCore component ⊆
      ledger.remainingCore
  containedInPiece :
    Connected.vertices object ledger.remainingCore component ⊆ piece.vertices
  containedInRemainder :
    Connected.vertices object ledger.remainingCore component ⊆
      object.remainderSupport packing
  connected : Connected.ConnectedOn object
    (Connected.vertices object ledger.remainingCore component)
  p13Free : InducedPathFree
    (object.induce (Connected.vertices object ledger.remainingCore component))
    presentation.inducedPathOrder
  contextualTargetSafe :
    TypeAB.ContextuallyDyadicSafe presentation object
  uncompressible : TypeAB.HereditarilyTargetUncompressible
    presentation object
      (Connected.vertices object ledger.remainingCore component)
  emptyInternalThreeCore : TypeAB.EmptyInternalThreeCore presentation object
    (Connected.vertices object ledger.remainingCore component)
  noBaselineSubsupport : ∀ inner : Finset object.Vertex,
    inner ⊆ Connected.vertices object ledger.remainingCore component →
      ¬ MinimumDegreeAtLeast threshold (object.induce inner)
  assignedSurplus_eq_zero : object.ambientSurplus
    (Connected.vertices object ledger.remainingCore component) threshold = 0
  reserveUnitsLiteral :
    refinedComponentReserveUnits ledger component ⊆ ledger.remainingReserve
  suppliedPositiveDeficiency :
    ((dischargeScale * object.positiveDeficiency
      (Connected.vertices object ledger.remainingCore component)
      threshold : Nat) : Int) ≤
      refinedComponentReserve ledger component +
        refinedComponentWindowStubReserve ledger component
  exactWeightedRefinement : ledger.ExactAugmentedLedgerRefinement

/-- A post-ledger component is already the admissible carrier expected by the
Type A rows.  The bridge reduction supplies the sign when it dispatches this
particular component; hygiene itself neither assumes nor manufactures it. -/
theorem PostLedgerComponent.typeASupportInput_of_negative
    {presentation : TypeAB.Presentation.{u}}
    {ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece}
    {component : Connected.Component object ledger.remainingCore}
    (componentData : PostLedgerComponent presentation ledger component)
    (negative : object.NegativeNetCharge
      (Connected.vertices object ledger.remainingCore component)
      threshold dischargeScale) :
    Connected.vertices object ledger.remainingCore component ⊆
        object.remainderSupport packing ∧
      Connected.ConnectedOn object
        (Connected.vertices object ledger.remainingCore component) ∧
      object.NegativeNetCharge
        (Connected.vertices object ledger.remainingCore component)
        threshold dischargeScale ∧
      object.ambientSurplus
        (Connected.vertices object ledger.remainingCore component) threshold = 0 :=
  ⟨componentData.containedInRemainder, componentData.connected, negative,
    componentData.assignedSurplus_eq_zero⟩

/-- Receiver routing is total on the retained post-ledger component because
the same remainder-normalization fact excludes every baseline sub-support. -/
theorem PostLedgerComponent.exists_traceTo
    {presentation : TypeAB.Presentation.{u}}
    {ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece}
    {component : Connected.Component object ledger.remainingCore}
    (componentData : PostLedgerComponent presentation ledger component)
    {source : object.Vertex}
    (member : source ∈ Connected.vertices object ledger.remainingCore component)
    (full : threshold ≤ object.internalDegree
      (Connected.vertices object ledger.remainingCore component) source) :
    ∃ target, object.TraceTo
      (Connected.vertices object ledger.remainingCore component)
      threshold source target :=
  object.exists_traceTo_of_no_baseline_subsupport
    (Connected.vertices object ledger.remainingCore component) threshold
    componentData.noBaselineSubsupport member full

/-- The canonical receiver map is total on the full-degree vertices of one
post-ledger component.  The receiver is selected by the existing
`traceReceiver?` tie-breaker, so this introduces no second routing choice. -/
theorem PostLedgerComponent.receiverRouting
    {presentation : TypeAB.Presentation.{u}}
    {ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece}
    {component : Connected.Component object ledger.remainingCore}
    (componentData : PostLedgerComponent presentation ledger component) :
    ∀ source ∈ Connected.vertices object ledger.remainingCore component,
      object.internalDegree
          (Connected.vertices object ledger.remainingCore component) source =
        threshold →
        ∃ receiver,
          object.traceReceiver?
              (Connected.vertices object ledger.remainingCore component)
              threshold source = some receiver ∧
            object.IsReceiver
              (Connected.vertices object ledger.remainingCore component)
              threshold receiver := by
  intro source member full
  obtain ⟨target, trace⟩ :=
    componentData.exists_traceTo member (Nat.le_of_eq full.symm)
  have routedSome := object.isSome_traceReceiver?_of_traceTo trace
  obtain ⟨receiver, routed⟩ := Option.isSome_iff_exists.mp routedSome
  exact ⟨receiver, routed,
    object.isReceiver_of_traceTo
      (object.traceTo_of_traceReceiver?_eq_some routed)⟩

/-- A selected post-ledger component either already has nonnegative Type A
charge or contains an actual saturated receiver.  The first arm is the exact
unsaturated-discharge inequality on that same canonical component. -/
theorem PostLedgerComponent.nonnegative_or_saturatedReceiver
    {presentation : TypeAB.Presentation.{u}}
    {ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece}
    {component : Connected.Component object ledger.remainingCore}
    (componentData : PostLedgerComponent presentation ledger component)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    (Connected.vertices object ledger.remainingCore component).card ≤
        dischargeScale * object.positiveDeficiency
          (Connected.vertices object ledger.remainingCore component) threshold ∨
      ∃ receiver,
        object.IsReceiver
            (Connected.vertices object ledger.remainingCore component)
            threshold receiver ∧
          object.Saturated
            (Connected.vertices object ledger.remainingCore component)
            threshold dischargeScale receiver := by
  let support := Connected.vertices object ledger.remainingCore component
  change support.card ≤
        dischargeScale * object.positiveDeficiency support threshold ∨
      ∃ receiver,
        object.IsReceiver support threshold receiver ∧
          object.Saturated support threshold dischargeScale receiver
  have capped : ∀ vertex ∈ support,
      object.internalDegree support vertex ≤ threshold := by
    intro vertex member
    have componentMember : vertex ∈
        Connected.vertices object ledger.remainingCore component := member
    have remainingMember : vertex ∈ ledger.remainingCore :=
      componentData.containedInRemainingCore componentMember
    have degreeLe : object.degree vertex ≤ threshold := by
      simpa [Graph.IsHighCentre] using
        (ledger.noHighCentre_remaining remainingMember)
    have degreeEq : object.degree vertex = threshold :=
      Nat.le_antisymm degreeLe (baseline vertex)
    calc
      object.internalDegree support vertex ≤ object.degree vertex :=
        object.internalDegree_le_degree support vertex
      _ = threshold := degreeEq
  have routes : ∀ vertex ∈ support,
      object.internalDegree support vertex = threshold →
        ∃ receiver,
          object.traceReceiver? support threshold vertex = some receiver ∧
            object.IsReceiver support threshold receiver := by
    exact componentData.receiverRouting
  by_cases saturated : ∃ receiver,
      object.IsReceiver support threshold receiver ∧
        object.Saturated support threshold dischargeScale receiver
  · exact Or.inr saturated
  · left
    have unsaturated : ∀ receiver,
        object.IsReceiver support threshold receiver →
          1 + object.routedLoad support threshold receiver ≤
            dischargeScale * object.missingPorts support threshold receiver := by
      intro receiver receiverIs
      rw [← object.not_saturated_iff support threshold dischargeScale receiver]
      intro receiverSaturated
      exact saturated ⟨receiver, receiverIs, receiverSaturated⟩
    exact object.unsaturatedDischarge support threshold dischargeScale capped
      routes unsaturated

/-- The exact live post-ledger hygiene theorem.  Its inputs are the inherited
facts of the incoming admissible support; every B2/reserve conclusion is read
from the same `ledger`. -/
theorem postLedgerCoreHygiene
    (presentation : TypeAB.Presentation.{u})
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : Connected.Component object ledger.remainingCore)
    (componentMember : component ∈ Connected.order object ledger.remainingCore)
    (baselineDegree : threshold = presentation.baselineDegree)
    (remainderNormalized : ∀ support : Finset object.Vertex,
      support ⊆ object.remainderSupport packing →
        ¬ MinimumDegreeAtLeast threshold (object.induce support))
    (p13Free : InducedPathFree (object.induce piece.vertices)
      presentation.inducedPathOrder)
    (contextualTargetSafe :
      TypeAB.ContextuallyDyadicSafe presentation object)
    (uncompressible : TypeAB.HereditarilyTargetUncompressible
      presentation object piece.vertices)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    PostLedgerComponent presentation ledger component := by
  have containedInPiece := refinedComponent_subset_piece ledger component
  have containedInRemainder :=
    containedInPiece.trans piece.vertices_subset_remainder
  have noBaselineSubsupport : ∀ inner : Finset object.Vertex,
      inner ⊆ Connected.vertices object ledger.remainingCore component →
        ¬ MinimumDegreeAtLeast threshold (object.induce inner) := by
    intro inner subset
    exact remainderNormalized inner (subset.trans containedInRemainder)
  exact {
    componentMember := componentMember
    containedInRemainingCore :=
      refinedComponent_subset_remainingCore ledger component
    containedInPiece := containedInPiece
    containedInRemainder := containedInRemainder
    connected := refinedComponent_connected ledger component componentMember
    p13Free := inducedPathFree_of_subset presentation.inducedPathOrder
      containedInPiece p13Free
    contextualTargetSafe := contextualTargetSafe
    uncompressible := hereditarilyTargetUncompressible_of_subset
      containedInPiece uncompressible
    emptyInternalThreeCore :=
      emptyInternalThreeCore_of_noBaselineSubsupport baselineDegree
        noBaselineSubsupport
    noBaselineSubsupport := noBaselineSubsupport
    assignedSurplus_eq_zero :=
      refinedComponent_ambientSurplus_eq_zero ledger component
    reserveUnitsLiteral := refinedComponentReserveUnits_subset ledger component
    suppliedPositiveDeficiency :=
      refinedComponent_positiveDeficiency_supplied ledger component baseline
    exactWeightedRefinement := ledger.exactAugmentedLedgerRefinement
    }

end

end Hypostructure.Graph.TypeBPostLedgerCore
